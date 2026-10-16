-- Prove2me | Theorems.Thm_MIPRE_Cost_Data_length_filter_flatMap_bits
-- name    : MIPRE.Cost.Data.length_filter_flatMap_bits
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:37:11.652751+00:00
-- url     : https://prove2.me/theorems/2da38a47-feb7-4716-a2bc-69b3dcaf6577
-- title:
--   Counting, in a list of bit strings each extended by a leading bit, those that satisfy a predicate
-- statement:
--   Let $L$ be a list of bit strings and $p$ a Boolean predicate on bit strings. Write $L^{+}$ for the list obtained from $L$ by replacing each string $l$ by the two strings $0 \cdot l$ and $1 \cdot l$, in this order (`L.flatMap fun l => [false :: l, true :: l]`); the enumeration of the bit strings of length $k + 1$ used by the tabulations is $(\mathrm{bitStrsOfLen}\ k)^{+}$. For a predicate $q$, $|\mathrm{filter}_q(L)|$ denotes the length of the sublist of $L$ of the elements satisfying $q$, with multiplicities.
--
--   $$ \bigl|\mathrm{filter}_{p}(L^{+})\bigr| \;=\; \bigl|\mathrm{filter}_{l \mapsto p(0 \cdot l)}(L)\bigr| + \bigl|\mathrm{filter}_{l \mapsto p(1 \cdot l)}(L)\bigr|. $$
--
--   This is the one-bit step of counting seeds by their prefix (`length_filter_take`): the class verifier of the polynomial-time halting reduction reads only the first $d$ bits of its seed of length $d + e$, so the number of seeds whose prefix satisfies a predicate is the number of prefixes that do, times $2^e$, which turns the verifier's seed count into the numerator of the compressed sampler's distribution.
--
--   **Formalization Note**. The statement is `MIPRE.Cost.Data.length_filter_flatMap_bits`, for `L : List BitStr` with `BitStr = List Bool` and `p : BitStr → Bool`; it is an equality of natural numbers between `((L.flatMap fun l => [false :: l, true :: l]).filter p).length` and `(L.filter fun l => p (false :: l)).length + (L.filter fun l => p (true :: l)).length`, with no hypotheses on `L` or `p`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/Count.lean#L23-L37; internal counting lemma for blueprint thm:halting at the fixed level (module docstring); no blueprint label is attached to this declaration

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
open MIPRE.Cost
open MIPRE.Cost.Data

theorem MIPRE.Cost.Data.length_filter_flatMap_bits (L : List BitStr) (p : BitStr → Bool) :
    ((L.flatMap fun l => [false :: l, true :: l]).filter p).length =
      (L.filter fun l => p (false :: l)).length + (L.filter fun l => p (true :: l)).length := by sorry
