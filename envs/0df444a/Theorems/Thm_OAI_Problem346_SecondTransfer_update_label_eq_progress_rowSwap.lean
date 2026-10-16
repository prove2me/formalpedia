-- Prove2me | Theorems.Thm_OAI_Problem346_SecondTransfer_update_label_eq_progress_rowSwap
-- name    : OAI.Problem346.SecondTransfer.update_label_eq_progress_rowSwap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:59:43.470976+00:00
-- url     : https://prove2.me/theorems/17a87a94-c5f9-43c0-ab95-b366031bd2dd
-- title:
--   Relabelling one source position as common equals advancing the row's prefix count, after a column swap
-- statement:
--   Fix natural numbers $r$ and $b$, the grid $G=\{0,1,\dots,r\}\times\{0,1,\dots,b-1\}$ of positions (row, column), and the block set $B_r=\{\star\}\cup\{0,1,\dots,r\}$, where $\star$ is a common block. For a count vector $k=(k_1,\dots,k_r)\in\mathbb{N}^r$ the prefix labelling $\ell_k:G\to B_r$ is given by $\ell_k(0,j)=0$ and, for $1\le i\le r$, by $\ell_k(i,j)=\star$ if $j<k_i$ and $\ell_k(i,j)=i$ if $j\ge k_i$.
--
--   Fix a row $i\in\{1,\dots,r\}$ with $k_i<b$ and a column $j$ with $k_i\le j\le b-1$, so that $(i,j)$ carries the row's own block $i$, and $k_i$ is the first column of row $i$ that does. Let
--
--   - $\ell_k^{(i,j)\to\star}$ be the labelling that agrees with $\ell_k$ except that position $(i,j)$ is relabelled by $\star$;
--   - $k+\delta_i$ be the count vector obtained from $k$ by replacing $k_i$ with $k_i+1$;
--   - $\sigma_a$, for each row $a\in\{0,\dots,r\}$, be the permutation of the columns $\{0,\dots,b-1\}$ with $\sigma_i=(j\ k_i)$, the transposition exchanging columns $j$ and $k_i$ (the identity if $j=k_i$), and $\sigma_a=\mathrm{id}$ for $a\ne i$.
--
--   **Theorem.** For every position $(a,l)\in G$,
--
--   $$
--   \ell_k^{(i,j)\to\star}(a,l)=\ell_{k+\delta_i}\bigl(a,\sigma_a(l)\bigr).
--   $$
--
--   In words: relabelling any one remaining source position of row $i$ by the common block gives the next prefix labelling, up to a permutation of the columns inside row $i$. Consequently, every quantity that is invariant under independent permutations of the columns within each row (for instance a multilinear form evaluated on the products, in a symmetric power, of the entries of each row) takes the same value on each of these single relabellings as on $\ell_{k+\delta_i}$. This is what turns the derivative of a labelled polynomial, which is a sum over all source positions, into a multiple of the next-stage polynomial.
--
--   **Formalization Note** The rows of $G$ are `Fin (r+1)`, and the moving row $i$ is `i.succ` for `i : Fin r`; blocks are `Option (Fin (r+1))` with `none` the common block. The relabelled labelling is `Function.update (label k) (i.succ, j) none`, the count vector $k+\delta_i$ is `Function.update k i (k i + 1)`, and the family $(\sigma_a)$ is `rowFactorSwap i j ⟨k i, hi⟩`, built from `Equiv.swap`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/SecondSwap.lean#L13-L49

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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondSwap

open OAI OAI.Problem346 OAI.Problem346.SecondTransfer

theorem OAI.Problem346.SecondTransfer.update_label_eq_progress_rowSwap
    {r b : ℕ} (k : Fin r → ℕ) (i : Fin r) (hi : k i < b)
    (j : Fin b) (hj : k i ≤ j.val) (p : Fin (r+1) × Fin b) :
    Function.update (label k) (i.succ, j) none p =
      label (Function.update k i (k i+1))
        (p.1, rowFactorSwap i j ⟨k i, hi⟩ p.1 p.2) := by sorry
