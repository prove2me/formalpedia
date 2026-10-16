-- Prove2me | Theorems.Thm_MIPRE_Verifier_mem_accListW_iff
-- name    : MIPRE.Verifier.mem_accListW_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:39:17.024985+00:00
-- url     : https://prove2.me/theorems/dc2dda78-55eb-4fed-8494-d59566bf28a3
-- title:
--   Membership in the acceptance table of a tabulated verifier
-- statement:
--   Let $s$ and $T$ be natural numbers, let $f_A, f_B : \{0,1\}^* \to \mathbb{N}$ be two indexings of questions (one per player), and let `acc?` be a Boolean predicate on quadruples $(x, y, a, b)$ of bit strings. The acceptance table `accListW s T fA fB acc?` is the list of quadruples of natural numbers $(f_A(x), f_B(y), \mathrm{idxOf}(a, \mathtt{bitStrsLE}\ T), \mathrm{idxOf}(b, \mathtt{bitStrsLE}\ T))$ for $x, y$ ranging over the bit strings of length exactly $s$ and $a, b$ over the bit strings of length at most $T$, an entry being present exactly when `acc? x y a b = true`. For all natural numbers $i, j, k, l$:
--
--   $$ (i, j, k, l) \in \mathtt{accListW}\ s\ T\ f_A\ f_B\ \mathtt{acc?} \iff \exists\, x, y \in \mathtt{bitStrsOfLen}\ s,\ \exists\, a, b \in \mathtt{bitStrsLE}\ T:\ \mathtt{acc?}\ x\ y\ a\ b = \mathtt{true} \,\wedge\, i = f_A(x) \,\wedge\, j = f_B(y) \,\wedge\, k = \mathrm{idxOf}(a, \mathtt{bitStrsLE}\ T) \,\wedge\, l = \mathrm{idxOf}(b, \mathtt{bitStrsLE}\ T). $$
--
--   The acceptance list of the game description tabulating a verifier (blueprint `rem:compression-abstract`, item 3) is `accListW` at two *tagged* indexings, Alice's question tagged with a `false` bit and Bob's with a `true` bit; this characterization is what every statement about the decision predicate of the tabulated game reduces to. `Verifier.accList s T acc?` is the special case $f_A = f_B = \mathtt{bitsToIdx}$ and is definitionally the same list.
--
--   **Formalization Note** `accListW` is defined by `flatMap` over `Data.bitStrsOfLen s` (for `x` and for `y`) and over `Data.bitStrsLE T` (for `a`), then a `filterMap` over `Data.bitStrsLE T` (for `b`) returning `some (fA x, fB y, (bitStrsLE T).idxOf a, (bitStrsLE T).idxOf b)` when `acc? x y a b` holds and `none` otherwise. Membership is list membership in `List (ℕ × ℕ × ℕ × ℕ)`; the existentials are bounded by list membership (`∃ x ∈ Data.bitStrsOfLen s, …`), equivalent to `x.length = s`, respectively `a.length ≤ T`; the four equations are oriented with the index on the left (`i = fA x`). All of `s T fA fB acc? i j k l` are implicit. The declaration has no docstring in the source. Namespace `MIPRE.Verifier`, module `MIPRE.Foundations.Halting.Tabulate`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Tabulate.lean#L509-L526

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
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
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate

open MIPRE
open MIPRE.Verifier
open MIPRE.Cost
open HaltingGameValue (GameData)

theorem MIPRE.Verifier.mem_accListW_iff {s T : ℕ} {fA fB : BitStr → ℕ}
    {acc? : BitStr → BitStr → BitStr → BitStr → Bool} {i j k l : ℕ} :
    (i, j, k, l) ∈ accListW s T fA fB acc? ↔
      ∃ x ∈ Data.bitStrsOfLen s, ∃ y ∈ Data.bitStrsOfLen s,
        ∃ a ∈ Data.bitStrsLE T, ∃ b ∈ Data.bitStrsLE T,
          acc? x y a b = true ∧ i = fA x ∧ j = fB y ∧
            k = (Data.bitStrsLE T).idxOf a ∧ l = (Data.bitStrsLE T).idxOf b := by sorry
