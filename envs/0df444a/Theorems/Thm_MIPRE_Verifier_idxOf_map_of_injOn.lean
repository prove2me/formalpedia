-- Prove2me | Theorems.Thm_MIPRE_Verifier_idxOf_map_of_injOn
-- name    : MIPRE.Verifier.idxOf_map_of_injOn
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:39:13.09528+00:00
-- url     : https://prove2.me/theorems/3229bbb8-911b-4592-9cc8-d1aae32c9dfc
-- title:
--   Index of a mapped element in a list, for a map injective on that list
-- statement:
--   Let $\alpha$ and $\beta$ be types with Boolean equality tests that agree with propositional equality (`BEq` with `LawfulBEq`). Let $f : \alpha \to \beta$ be a function, $l$ a list of elements of $\alpha$, and suppose $f$ is injective on the members of $l$: for all $x, y \in l$, $f(x) = f(y)$ implies $x = y$. For $x \in l$, write $\mathrm{idxOf}(x, l)$ for the index of the first occurrence of $x$ in $l$. Then the index of $f(x)$ in the mapped list is the index of $x$ in the original list:
--
--   $$ \mathrm{idxOf}\bigl(f(x),\ \mathrm{map}\ f\ l\bigr) \;=\; \mathrm{idxOf}(x,\ l). $$
--
--   The lemma is general-purpose list bookkeeping. In the tabulation of a verifier it serves `Verifier.answerEquiv_symm_val`: the enumeration of the answers is the enumeration of the bit strings of length at most $T$ mapped through a truncation that is injective on that list, so the position of an answer among the answers is its position among the bit strings.
--
--   **Formalization Note** The statement is `(l.map f).idxOf (f x) = l.idxOf x`, with `List.idxOf` taken with respect to the `BEq` instances of `α` and `β`, both assumed lawful (`[BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]`); `List.idxOf a l` returns the length of `l` when `a` does not occur in it. Injectivity is required only on the members of `l` (`hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y`), not globally, and `hx : x ∈ l` is a hypothesis; `x` is implicit, `f` and `l` explicit, and the types live in arbitrary universes (`Type*`). Although declared in namespace `MIPRE.Verifier` (module `MIPRE.Foundations.Halting.Tabulate`), nothing in it refers to verifiers.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Tabulate.lean#L318-L333

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

theorem MIPRE.Verifier.idxOf_map_of_injOn {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (l : List α) (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) {x : α} (hx : x ∈ l) :
    (l.map f).idxOf (f x) = l.idxOf x := by sorry
