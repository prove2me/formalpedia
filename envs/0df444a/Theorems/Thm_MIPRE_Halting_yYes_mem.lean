-- Prove2me | Theorems.Thm_MIPRE_Halting_yYes_mem
-- name    : MIPRE.Halting.yYes_mem
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:39:11.303402+00:00
-- url     : https://prove2.me/theorems/a047f000-6b2f-4e0d-bd3b-a25e2a620514
-- title:
--   Obligation O1, the accepting side: the string $y_{\mathrm{yes}}$ lies in the class $A$ at every level from some $n_0$ on
-- statement:
--   Fix a gap-preserving compression $G$ (`GapCompression`, with compressed sampler $\mathcal S^{\mathrm{compr}}_\lambda$ = `G.sampler lam` and bounding polynomial $\mathrm{bound}$ = `G.bound`) and an efficient universal machine $U$. A bit string denotes a pair (parameter, decider) through the postorder serialization of data, and the verifier `Vof G U x` it denotes is the compressed sampler at the string's parameter with the string's decider, run by the universal machine and wrapped in the question-length check. The string $y_{\mathrm{yes}}$ = `yYes` is the description `descOf 0 decYes` of the parameter $0$ and the fixed-answer decider `decYes`, which accepts exactly the empty answer from both players (`decYes_runs_true_iff`); it denotes the verifier $(\mathcal S^{\mathrm{compr}}_0, \mathrm{wrap}\ \mathrm{decYes})$, with answer cut `ansBound G yYes n` = $\mathrm{bound}(n)$. The class $A$ at level $n$ (`classA G U n`) is the set of strings $x$ whose verifier is $n$-bounded (`IsBounded n`), rejects every answer longer than `ansBound G x n` at index $n$ (`RejectsLong`), and whose $n$-th game with answers of length at most `ansBound G x n` has a value-1 PCC strategy (`HasPerfectPCC`, on the doubled game).
--
--   $$ \exists\, n_0 \in \mathbb N,\ \forall n \ge n_0,\qquad y_{\mathrm{yes}} \in \mathrm{classA}_{G, U}(n). $$
--
--   This is the accepting half of obligation O1 of the halting reduction (`Halting/Reduction.lean` applies it directly; the rejecting half is `yNo_mem`). As the docstring records, the constant strategy answering the empty string is the value-1 PCC strategy, and every long answer is rejected because only the empty answers are accepted.
--
--   **Formalization Note**. The theorem is `MIPRE.Halting.yYes_mem`, with $G$, $U$ explicit and conclusion `∃ n₀, ∀ n, n₀ ≤ n → yYes ∈ classA G U n`; membership unfolds to `(Vof G U yYes).InClassA n (ansBound G yYes n)`, i.e. `IsBounded n ∧ RejectsLong n T ∧ HasPerfectPCC n T` with `T = ansBound G yYes n = G.bound.eval (n + 0)`, and `Vof G U yYes` is `Verifier.ofSamplerDecider U (G.sampler 0) decYes` (`Vof_yYes`). The threshold $n_0$ is existential, not computed; the module docstring attributes the boundedness clause to `Verifier.ofSamplerDecider_isBounded`, whose hypotheses are the polynomial cost bounds of the sampler (fields of `GapCompression`) and of `decYes`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Strings.lean#L169-L188; internal lemma of the formalization of blueprint thm:halting (obligation O1 of the halting reduction, the two distinguished strings)

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Halting
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
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings

open MIPRE
open MIPRE.Halting
open MIPRE.Cost
variable (G : GapCompression) (U : UniversalMachine)

theorem MIPRE.Halting.yYes_mem : ∃ n₀, ∀ n, n₀ ≤ n → yYes ∈ classA G U n := by sorry
