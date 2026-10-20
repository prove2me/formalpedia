-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_exists_small_dyadic_difference
-- name    : OAI.LipschitzCounterexample.CompactWSC.exists_small_dyadic_difference
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:13:17.930878+00:00
-- url     : https://prove2.me/theorems/ebfdd4a4-879b-4f59-9e2b-a00cf8ce0498
-- title:
--   Some dyadic difference has small quadratic size
-- statement:
--   Let $Q\ge0$ be a function on a real vector space satisfying the midpoint identity
--   $$
--   Q\Bigl(\tfrac{x+y}2\Bigr)=\frac{Q(x)+Q(y)}2-\frac{Q(x-y)}4 .
--   $$
--   Let $u_0,\dots,u_{2^d-1}$ satisfy $Q(u_k)\le C$, and let $\varepsilon>0$ with $4C<d\varepsilon$. Then some level $n<d$ and index $k$ with $k+2^{n+1}\le2^d$ satisfy
--   $$
--   Q\bigl(m_n(k)-m_n(k+2^n)\bigr)<\varepsilon ,
--   $$
--   where $m_n(k)$ is the average of $u_k,\dots,u_{k+2^n-1}$.
--
--   For $Q=\|\cdot\|^2$ in a Hilbert space the midpoint identity is the parallelogram law.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/HilbertBlocks.lean#L76-L93

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uE uF uH
open scoped BigOperators
variable {E : Type uE} [AddCommGroup E] [Module ℝ E]
variable {F : Type uF} [AddCommGroup F] [Module ℝ F]

theorem OAI.LipschitzCounterexample.CompactWSC.exists_small_dyadic_difference (Q : E → ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (hmid : ∀ x y, Q ((1/2 : ℝ) • (x+y)) = (Q x+Q y)/2-Q (x-y)/4)
    (u : ℕ → E) {C ε : ℝ} (_hε : 0 < ε) (d : ℕ) (hd : 4*C < (d : ℝ)*ε)
    (hu : ∀ k < 2^d, Q (u k) ≤ C) :
    ∃ n k, n < d ∧ k+2^(n+1) ≤ 2^d ∧
      Q (dyadicMean u n k-dyadicMean u n (k+2^n)) < ε := by sorry
