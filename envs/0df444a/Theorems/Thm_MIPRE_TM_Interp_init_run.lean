-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_init_run
-- name    : MIPRE.TM.Interp.init_run
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:24:06.623632+00:00
-- url     : https://prove2.me/theorems/a909adad-f59e-4488-9b3d-31fdea8c2998
-- title:
--   The initialization: from the initial configuration on the inputs (𝒟, n, T, x, y, a, b) with |a|, |b| ≤ T, U reaches the dispatcher representing ⟨ev 𝒟, [encode (n, x, y,…
-- statement:
--   A statement of the module `MIPRE.TM.Interp.Run` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The run of the interpreter. The inputs of `U` (`uInput`), the initialization (`init_run`), the simulation of a run of the evaluation machine (`sim_run`), and the acceptance theorem: on the inputs `(𝒟, n, T, x, y, a, b)` with `|a|, |b| ≤ T`, `U` accepts (halts having output `1`) iff `𝒟` accepts `(n, x, y, a, b)` within cost `T`, and then within an explicit polynomial number of steps.
--
--   **The initialization**: from the initial configuration on the inputs `(𝒟, n, T, x, y, a, b)`
--   with `|a|, |b| ≤ T`, `U` reaches the dispatcher representing `⟨ev 𝒟, [encode (n, x, y, a, b)], []⟩`
--   with budget `Tb` and an empty scratch tape.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.Interp
--   open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
--   open MultiTapeTM (moveInputPos)
--   variable {input : Fin 7 → List Sym}
--
--   theorem MIPRE.TM.Interp.init_run (D : Prog) (n : ℕ) (x y a b : BitStr) (Tb : ℕ) (ha : a.length ≤ Tb)
--       (hb : b.length ≤ Tb) :
--       ∃ m ≤ initBound D n x y a b Tb, ∃ (c : Cfg (uInput D n Tb x y a b)) (ds : WT → TapeSt),
--         Reach (U.initCfg (uInput D n Tb x y a b)) m c [] ∧ Desc c (at_ .dispatch 0) ds ∧
--         RepOf ds ⟨.ev D, [encode (n, x, y, a, b)], []⟩ Tb (ctrlRepr (.ev D)).length 0 ∧
--         (ds X).l.length = 0
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.init_run` is declared in `MIPRE/TM/Interp/Run.lean`, lines 274–357. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Run.lean#L274-L357

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Definitions.Def_MIPRE_TM_Interp_Run

open MIPRE
open MIPRE.TM
open MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}

theorem MIPRE.TM.Interp.init_run (D : Prog) (n : ℕ) (x y a b : BitStr) (Tb : ℕ) (ha : a.length ≤ Tb)
    (hb : b.length ≤ Tb) :
    ∃ m ≤ initBound D n x y a b Tb, ∃ (c : Cfg (uInput D n Tb x y a b)) (ds : WT → TapeSt),
      Reach (U.initCfg (uInput D n Tb x y a b)) m c [] ∧ Desc c (at_ .dispatch 0) ds ∧
      RepOf ds ⟨.ev D, [encode (n, x, y, a, b)], []⟩ Tb (ctrlRepr (.ev D)).length 0 ∧
      (ds X).l.length = 0 := by sorry
