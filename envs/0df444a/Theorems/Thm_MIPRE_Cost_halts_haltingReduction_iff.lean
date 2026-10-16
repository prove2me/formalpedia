-- Prove2me | Theorems.Thm_MIPRE_Cost_halts_haltingReduction_iff
-- name    : MIPRE.Cost.halts_haltingReduction_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:25:28.96461+00:00
-- url     : https://prove2.me/theorems/a8395bfb-9fe7-4d32-9309-c41dd5dc3705
-- title:
--   The polynomial-time halting reduction halts on the empty input exactly when the semidecider halts
-- statement:
--   Let $S$ be a program of the ambient model that is closed with one input (`S.WellScoped 1`: every variable is bound in a one-entry environment) and $z$ a bit string. `Halts p x` means $\exists\, r\, t,\ \mathrm{Eval}\ [x]\ p\ r\ t$: $p$ halts on the input $x$. `haltingReduction S : PolyTimeFun BitStr Prog` is the polynomial-time function $z \mapsto \mathrm{hardcode}\ (\mathrm{onLeft}\ S)\ (\mathrm{encode}\ z)$: `hardcode p d` is the s-m-n transformation, the program running $p$ on the pair `cons d input`, and `onLeft p` is the program that on an input `cons d v` runs $p$ on $d$ (and on `nil` halts with `nil`). Then
--
--   $$\mathrm{Halts}\ (\mathrm{haltingReduction}\ S\ z)\ \mathrm{nil} \iff \mathrm{Halts}\ S\ (\mathrm{encode}\ z).$$
--
--   With `exists_semidecider`, which turns an r.e. predicate on strings into such an $S$ halting exactly on its members, this gives `exists_polyTime_reduction`: every r.e. predicate on strings many-one reduces, in polynomial time, to halting on the empty input. This is the reduction the polynomial-time halting instance of the MIP* = RE argument consumes.
--
--   **Formalization Note** `haltingReduction S z` is definitionally `hardcode (Prog.onLeft S) (encode z)` (`haltingReduction_apply`); the `PolyTimeFun` structure carrying the program and its time bound is coerced to its function. `encode z` for a bit string is the list encoding `Data.ofList Data.ofBool z`, and `.nil` is the empty datum. The hypothesis `hS : S.WellScoped 1` is required and `S` is implicit; no running-time bound appears in the statement, which is about halting only.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/ManyOne.lean#L43-L64

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_Cost_ManyOne

open MIPRE
open MIPRE.Cost

theorem MIPRE.Cost.halts_haltingReduction_iff {S : Prog} (hS : S.WellScoped 1) (z : BitStr) :
    Halts (haltingReduction S z) .nil ↔ Halts S (encode z) := by sorry
