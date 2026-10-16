-- Prove2me | Theorems.Thm_OAI_Problem346_SecondTransfer_source_occurrences
-- name    : OAI.Problem346.SecondTransfer.source_occurrences
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:57:26.029999+00:00
-- url     : https://prove2.me/theorems/545f2496-9d29-4421-8429-48971cfc0255
-- title:
--   Occurrences of a row's own block in the prefix labelling of an $(r+1)\times b$ grid
-- statement:
--   Fix natural numbers $r$ and $b$, and consider the grid of positions $G=\{0,1,\dots,r\}\times\{0,1,\dots,b-1\}$; the first coordinate of a position is its row and the second its column. Positions are labelled by blocks from $B_r=\{\star\}\cup\{0,1,\dots,r\}$, where $\star$ is a distinguished common block. A count vector $k=(k_1,\dots,k_r)\in\mathbb{N}^r$ determines the prefix labelling $\ell_k:G\to B_r$,
--
--   $$
--   \ell_k(0,j)=0,\qquad \ell_k(i,j)=\begin{cases}\star, & j<k_i,\\ i, & j\ge k_i,\end{cases}\qquad (1\le i\le r,\ 0\le j\le b-1).
--   $$
--
--   Thus row $0$ carries block $0$ throughout, and in a row $i\ge 1$ the first $k_i$ columns carry the common block while the remaining columns carry the row's own block $i$.
--
--   **Theorem.** Suppose $k_{i'}\le b$ for every $i'\in\{1,\dots,r\}$. Then for every $i\in\{1,\dots,r\}$ the number of positions labelled by block $i$ is
--
--   $$
--   \#\{(a,j)\in G:\ \ell_k(a,j)=i\}=b-k_i .
--   $$
--
--   When a polynomial is attached to a labelling by giving all positions with the same label the same vector variable, the number of positions carrying a block is the degree of the polynomial in that block's variables. This count (the degree of the source block $i$) is compared with the number $\sum_{i'}k_{i'}$ of common positions to verify the positive-weight condition under which a derivation shifting degree from block $i$ to the common block can be cancelled.
--
--   **Formalization Note** In Lean the moving rows are indexed by `i : Fin r`, standing for row `i.succ`, and `k i` is the count of that row; blocks are `Option (Fin (r+1))`, with `none` the common block and `some a` the block of row `a`. The left-hand side is written as a sum of indicator values over `Fin (r+1) × Fin b`, and $b-k_i$ is natural-number subtraction, which is exact because $k_i\le b$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/SecondCounts.lean#L51-L70

import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondLabels

open OAI OAI.Problem346 OAI.Problem346.SecondTransfer
open scoped BigOperators

theorem OAI.Problem346.SecondTransfer.source_occurrences {r b : ℕ} (k : Fin r → ℕ)
    (hk : ∀ i, k i ≤ b) (i : Fin r) :
    (∑ p : Fin (r+1) × Fin b, if label k p = some i.succ then 1 else 0) = b-k i := by sorry
