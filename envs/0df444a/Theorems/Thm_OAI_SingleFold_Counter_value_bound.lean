-- Prove2me | Theorems.Thm_OAI_SingleFold_Counter_value_bound
-- name    : OAI.SingleFold.Counter.value_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:33:57.457274+00:00
-- url     : https://prove2.me/theorems/07fbd401-0650-4fbf-bd87-8d346d2a9862
-- title:
--   Counters grow by at most one per step
-- statement:
--   For a counter machine with input $d$ and every counter $j$,
--   $$
--   \mathrm{value}_j\bigl(\mathrm{run}(d,t)\bigr)\le d_j+t\qquad\text{for all }t .
--   $$
--
--   This bounds every counter by the input size plus the running time. It is used to choose a base $B$ larger than all counter values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/CounterMachine.lean#L46-L66

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine

open OAI OAI.SingleFold OAI.SingleFold.Counter
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]

omit [DecidableEq Q] in
theorem OAI.SingleFold.Counter.value_bound (M : Machine Q J) (d : J → ℕ) (t : ℕ) (j : J) : (run M d t).value j ≤ d j+t := by sorry
