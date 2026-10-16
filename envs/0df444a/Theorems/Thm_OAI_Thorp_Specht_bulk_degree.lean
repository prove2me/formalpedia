-- Prove2me | Theorems.Thm_OAI_Thorp_Specht_bulk_degree
-- name    : OAI.Thorp.Specht.bulk_degree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:34:51.435983+00:00
-- url     : https://prove2.me/theorems/4569dbb1-fc96-4adc-925d-c908a7c0e0c4
-- title:
--   Specht modules whose shape has defect above $n/4$ have dimension at least $2^{\lfloor n/16\rfloor}$
-- statement:
--   Let $n\ge 1$. Let $\lambda=(\lambda_1\ge\lambda_2\ge\dots\ge\lambda_\ell>0)$ be a partition of $n$ with $\ell=\ell(\lambda)$ parts, and let $D_\lambda$ be its Young diagram (row $r$ consists of the cells $(r,0),\dots,(r,\lambda_{r+1}-1)$). The longest line of the diagram has length $L(\lambda)=\max(\lambda_1,\ell(\lambda))$, the larger of the first-row length and the first-column length, and the *defect* of $\lambda$ is
--   $$\operatorname{def}(\lambda)=n-L(\lambda),$$
--   the number of cells outside the longer of the first row and the first column. Let $S^\lambda$ be the Specht module of shape $\lambda$: fix a bijection $t:\{0,\dots,n-1\}\to D_\lambda$; a tabloid is a function $f=\mathrm{row}\circ t\circ g$ with $g\in S_n$, on which $S_n$ acts by $(g\cdot f)(x)=f(g^{-1}x)$; the polytabloid is $e_t=\sum_{\sigma\in C_t}\operatorname{sgn}(\sigma)\,\delta_{\sigma\cdot(\mathrm{row}\circ t)}$, where $C_t$ is the group of permutations preserving $\mathrm{col}\circ t$; and $S^\lambda$ is the span of the translates $g\cdot e_t$ inside the space $\mathbb{C}^{\{\text{tabloids}\}}$. It is the irreducible representation of $S_n$ indexed by $\lambda$.
--
--   If $n<4\operatorname{def}(\lambda)$, then
--
--   $$
--   2^{\lfloor n/16\rfloor}\le\dim_{\mathbb{C}}S^\lambda .
--   $$
--
--   Partitions of defect greater than $n/4$ are the shapes far from both a single row and a single column, which form the bulk of all partitions of $n$. The theorem says that every one of them indexes an irreducible representation of $S_n$ of exponentially large dimension, so that, combined with a subexponential bound on the number of partitions, their total contribution to the sum $\sum_{\lambda\vdash n}1/\dim S^\lambda$ tends to $0$ as $n\to\infty$.
--
--   **Formalization Note** The partition is `p : NShape n` (a partition of `Fintype.card (Fin n)`), its diagram is `ofPartition p`, $\operatorname{def}(\lambda)$ is `defect p = n - longest (ofPartition p)` (natural-number subtraction, which is exact since $L(\lambda)\le n$), and $\dim S^\lambda$ is `degree p`, the `Module.finrank ℂ` of the Specht module built from the fixed bijection `canonicalTableau p`. The exponent $\lfloor n/16\rfloor$ is the natural-number quotient `n / 16`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/DegreeBounds.lean#L203-L217

import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_DegreeBounds

open OAI OAI.Thorp OAI.Thorp.Specht
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter
open scoped Classical
open Thorp.Young

theorem OAI.Thorp.Specht.bulk_degree {n : ℕ} (p : NShape n) (hn : 0 < n) (hu : n < 4 * defect p) :
    (2 : ℝ) ^ (n / 16) ≤ degree p := by sorry
