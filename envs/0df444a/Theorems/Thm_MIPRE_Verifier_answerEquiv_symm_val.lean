-- Prove2me | Theorems.Thm_MIPRE_Verifier_answerEquiv_symm_val
-- name    : MIPRE.Verifier.answerEquiv_symm_val
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:39:15.329675+00:00
-- url     : https://prove2.me/theorems/2cca5639-5b17-49fc-b552-bbdabbac7c2c
-- title:
--   The index of an answer is its position among the bit strings of length at most $T$
-- statement:
--   Fix a natural number $T$. The answer alphabet of the game $\mathcal{V}_n$ of a normal form verifier with answers cut at length $T$ is `Answers T`, the type of bit strings of length at most $T$. `Data.bitStrsLE T` is the list of all bit strings of length at most $T$ without repetition (the strings of length $0, 1, \dots, T$ in turn). The list `answerList T` is `bitStrsLE T` mapped through `toAnswer T`, truncation to length $T$, which is the identity on these strings, and `answerEquiv T` is the equivalence between `Fin (answerList T).length` and `Answers T` indexing each answer by its position in `answerList T`. For every answer $a$ with underlying bit string $a.\mathrm{val}$:
--
--   $$ \bigl((\mathtt{answerEquiv}\ T)^{-1}(a) : \mathbb{N}\bigr) \;=\; \mathrm{idxOf}\bigl(a.\mathrm{val},\ \mathtt{bitStrsLE}\ T\bigr). $$
--
--   This is how the tabulation of a verifier names answers by numbers: the answer alphabet of a `GameData` is `Fin (nA + 1)`, and the acceptance table `accListW` records the position of each accepted answer in `bitStrsLE T`; the lemma identifies that position with the index along which the agreement of the tabulated value with $\mathrm{val}^*(\mathcal{V}_n)$ is read, namely `answerEquiv`.
--
--   **Formalization Note** `Answers T` is the subtype `{a : BitStr // a.length ≤ T}` with `BitStr = List Bool`, and `a.1` is the underlying string. `toAnswer T l = ⟨l.take T, _⟩`, `answerList T = (Data.bitStrsLE T).map (toAnswer T)`, and `answerEquiv T : Fin (answerList T).length ≃ Answers T` is noncomputable, built by `List.Nodup.getEquivOfForallMemList` from the facts that `answerList T` has no duplicates and contains every answer. The left side is the `Fin` value coerced to `ℕ`; `List.idxOf` is with respect to the `BEq` of `List Bool`. `T` and `a` are explicit and there are no further hypotheses. Namespace `MIPRE.Verifier`, module `MIPRE.Foundations.Halting.Tabulate`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Tabulate.lean#L335-L351

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

theorem MIPRE.Verifier.answerEquiv_symm_val (T : ℕ) (a : Answers T) :
    (((answerEquiv T).symm a : Fin (answerList T).length) : ℕ) = (Data.bitStrsLE T).idxOf a.1 := by sorry
