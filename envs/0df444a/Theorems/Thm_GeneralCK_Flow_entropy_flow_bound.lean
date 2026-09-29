-- Prove2me | Theorems.Thm_GeneralCK_Flow_entropy_flow_bound
-- name    : GeneralCK.Flow.entropy_flow_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:21:49.71954+00:00
-- url     : https://prove2.me/theorems/8c714fd3-39f7-436e-a3d0-ebb413419617
-- title:
--   The finite Bellman inequality controls the regularized entropy flow
-- statement:
--   Assume FiniteHybridBellman. For every Boolean function $f$, every $0<\varepsilon<1/2$, and every $T\ge0$, let $\delta_{f,\varepsilon}$ be the regularized entropy-flow quantity. Then $$H(q_\varepsilon(T))\le\delta_{f,\varepsilon}(T).$$ The proof combines the static energy estimate, the generator identity, and scalar entropy comparison.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EntropyFlow.lean#L147-L158

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_cube_analysis
import Definitions.Def_GeneralCK_entropy_comparison
import Definitions.Def_GeneralCK_entropy_flow
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
namespace GeneralCK.Flow
end GeneralCK.Flow
open GeneralCK GeneralCK.Flow
open scoped BigOperators
open CubeAnalysis

theorem GeneralCK.Flow.entropy_flow_bound (hB : FiniteHybridBellman) {n : ℕ} (f : Cube n → Bool)
    {eps T : ℝ} (he : 0 < eps) (he' : eps < 1 / 2) (hT : 0 ≤ T) :
    H (Comparison.noiseParameter eps T) ≤ delta f eps T := by sorry
