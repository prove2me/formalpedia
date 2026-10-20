-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_Criterion_assemble
-- name    : OAI.LipschitzCounterexample.Criterion.assemble
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:30:59.102912+00:00
-- url     : https://prove2.me/theorems/ff6f0f71-265f-48a2-abbd-22926adfa549
-- title:
--   Assembling the Lipschitz-equivalent, non-isomorphic Banach spaces
-- statement:
--   Let $U$ be a separable real Banach space and $W=U\oplus_2\ell^2$. Suppose:
--   - $h:W\to U$ is a bijection with $h(0)=0$, $h$ is $\frac{26}{25}$-Lipschitz and $h^{-1}$ is $\frac{25}{24}$-Lipschitz;
--   - $q:\mathcal F(W)\to U$ is a bounded operator with $\|q\|\le\frac{51}{25}$ and $q(\delta_x)=h(x)-x_U$;
--   - $\mathcal F(W)$ is weakly sequentially complete and $q$ is completely continuous.
--
--   Then the main claim holds: there are separable Banach spaces $X,Y$ and a bijection $\Psi:X\to Y$ with
--   $$
--   \tfrac4{21}\|s-t\|\le\|\Psi(s)-\Psi(t)\|\le\tfrac{76}{25}\|s-t\| ,
--   $$
--   $X$ contains an isometric copy of $c_0(\ell^2)$, $Y$ contains no isomorphic copy of $c_0(\ell^2)$, and hence $X,Y$ are not linearly isomorphic.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/BanachAssembly.lean#L46-L84

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.Criterion
universe uE uX uY
open WeakSequences
open scoped NNReal

theorem OAI.LipschitzCounterexample.Criterion.assemble {U : Type} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U]
    (q : Free U RealL2 →L[ℝ] U)
    (h : Domain U RealL2 ≃ U)
    (hlin : ∀ x : Domain U RealL2, q (FreeSpace.point x) = h x - x.fst)
    (h0 : h 0 = 0)
    (hh : LipschitzWith (26/25) h) (hi : LipschitzWith (25/24) h.symm)
    (hq : ‖q‖ ≤ 51/25)
    (hA : WeakSequentiallyComplete (Free U RealL2))
    (hcc : CompletelyContinuous q) : MainClaim := by sorry
