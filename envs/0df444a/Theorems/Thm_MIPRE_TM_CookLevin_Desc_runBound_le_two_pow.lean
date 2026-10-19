-- Prove2me | Theorems.Thm_MIPRE_TM_CookLevin_Desc_runBound_le_two_pow
-- name    : MIPRE.TM.CookLevin.Desc.runBound_le_two_pow
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:19:37.183479+00:00
-- url     : https://prove2.me/theorems/e034a799-0e48-4b77-bab5-60a5d2cfbb5d
-- title:
--   The run of the interpreter machine fits in the tableau: under the validity hypotheses and |a|, |b| ≤ T, its accepting run is at most Sof (eOf T σ) steps
-- statement:
--   A statement of the module `MIPRE.TM.CookLevin.Params` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The parameters of the describer: the check circuit and the tableau length. Two constants and one choice. * `chk` is the check circuit of the interpreter machine: the truth-table circuit (`Fml.table`) of its local check predicate `checkPred U 1`, of `winCard 7 6 Sym Ctl` inputs and at most `7 · 2 ^ winCard` gates — an enormous constant, exactly as the paper's `lem:pack-check-size`, and formally harmless. `chk_isCheckCircuit` is the hypothesis of `lem:correct-tableau`; `Gc` is its gate count. * `eOf T σ = 5 (⌈log T⌉ + ⌈log σ⌉) + 24` is the exponent of the tableau length: under the validity…
--
--   **The run of the interpreter machine fits in the tableau**: under the validity hypotheses
--   and `|a|, |b| ≤ T`, its accepting run is at most `Sof (eOf T σ)` steps.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.CookLevin
--   open MIPRE.TM.CookLevin.Desc
--   open MIPRE.TM.Interp MIPRE.SAT MIPRE.Cost
--
--   theorem MIPRE.TM.CookLevin.Desc.runBound_le_two_pow (D : Prog) (n T Q σ : ℕ) (x y a b : BitStr)
--       (hV : Valid D n T Q σ x y) (ha : a.length ≤ T) (hb : b.length ≤ T) :
--       runBound D n x y a b T ≤ Sof (eOf T σ)
--   ```
--
--   **Formalization Note** `MIPRE.TM.CookLevin.Desc.runBound_le_two_pow` is declared in `MIPRE/TM/CookLevin/Params.lean`, lines 236–253. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Params.lean#L236-L253

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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds
import Definitions.Def_MIPRE_TM_CookLevin_Families
import Definitions.Def_MIPRE_TM_CookLevin_Window
import Definitions.Def_MIPRE_TM_CookLevin_FamilyFml
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
import Definitions.Def_MIPRE_Foundations_SAT_Table
import Definitions.Def_MIPRE_TM_CookLevin_Params

open MIPRE
open MIPRE.TM
open MIPRE.TM.CookLevin
open MIPRE.TM.CookLevin.Desc
open MIPRE.TM.Interp MIPRE.SAT MIPRE.Cost

theorem MIPRE.TM.CookLevin.Desc.runBound_le_two_pow (D : Prog) (n T Q σ : ℕ) (x y a b : BitStr)
    (hV : Valid D n T Q σ x y) (ha : a.length ≤ T) (hb : b.length ≤ T) :
    runBound D n x y a b T ≤ Sof (eOf T σ) := by sorry
