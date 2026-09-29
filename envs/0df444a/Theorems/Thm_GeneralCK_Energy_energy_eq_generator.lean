-- Prove2me | Theorems.Thm_GeneralCK_Energy_energy_eq_generator
-- name    : GeneralCK.Energy.energy_eq_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:21:40.439435+00:00
-- url     : https://prove2.me/theorems/128e5818-576e-4718-b039-47fd81d0cb97
-- title:
--   Recursive cube energy equals the mean entropy-generator pairing
-- statement:
--   For every dimension $n$ and every real-valued array $v$ on the Boolean cube, $$E_n(v)=\mathbb E_x\left[J(v(x))\sum_{i=1}^n(v(x^{(i)})-v(x))\right].$$ Here $E_n$ is the source recursive edge energy and $x^{(i)}$ flips coordinate $i$. This algebraic identity imposes no range restriction on $v$.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EnergyIdentity.lean#L40-L71

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
import Definitions.Def_GeneralCK_energy_generator
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
namespace GeneralCK.Energy
end GeneralCK.Energy
open GeneralCK GeneralCK.Energy
open scoped BigOperators
open CubeAnalysis

theorem GeneralCK.Energy.energy_eq_generator (n : ℕ) (v : Cube n → ℝ) :
    energy n v = mean (fun x => J (v x) * ∑ i, (v (flip x i) - v x)) := by sorry
