-- Prove2me | Theorems.Thm_MIPRE_Verifier_rePred_not_isBounded
-- name    : MIPRE.Verifier.rePred_not_isBounded
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:38:35.348924+00:00
-- url     : https://prove2.me/theorems/fb0e91e7-cdc6-4d21-ba9e-0752798f7d4b
-- title:
--   For a computably presented family of verifiers, the violation of $\lambda$-boundedness is recursively enumerable
-- statement:
--   A family $a \mapsto \mathcal V^a$ of normal form verifiers with $\ell$ levels, indexed by a `Primcodable` type $\alpha$, is computably presented (`Verifier.ComputablyPresented V`) when three functions are computable in Mathlib's sense (`Computable`): $a \mapsto \mathrm{encode}(\mathcal S^a.\mathrm{prog})$ and $a \mapsto \mathrm{encode}(\mathcal D^a.\mathrm{prog})$, the programs of the sampler and of the decider of $\mathcal V^a$ as the data that encode them, and $(a, n) \mapsto s^a(n)$, the dimension of the sampler's ambient space $\mathbb F_2^{s^a(n)}$. A verifier is $\lambda$-bounded (`IsBounded lam`, blueprint `def:lambda-bounded`) when for every $n \ge 2$ its sampler's dimension is at most $n^\lambda$ and its sampler and decider halt within cost $n^\lambda(|d| + 1)^\lambda$ on every input $(n, d)$, and its description length is at most $\lambda$. A predicate is recursively enumerable (`REPred`) when it is the domain of a partial computable function.
--
--   For every computably presented family $\mathcal V$:
--
--   $$ \mathrm{REPred}\bigl((a, \lambda) \mapsto \neg\,(\mathcal V^a \text{ is } \lambda\text{-bounded})\bigr)\qquad\text{on } \alpha \times \mathbb N . $$
--
--   This is blueprint `lem:bounded-violation-re`. It is the first of the three disjuncts of `Verifier.not_inClassB_iff` (the verifier a string denotes is not $n$-bounded, or its decider accepts an answer longer than the answer bound, or its $n$-th game has value above $\tfrac12$), whose union is the complement of the class $B$ at level $n$ that obligation O3 of the halting reduction asks a closed program to semidecide exactly.
--
--   **Formalization Note**. The theorem is `MIPRE.Verifier.rePred_not_isBounded {α : Type*} [Primcodable α] {ℓ : ℕ} {V : α → Verifier ℓ} (hV : ComputablyPresented V) : REPred fun q : α × ℕ => ¬ (V q.1).IsBounded q.2`. `ComputablyPresented` is a `Prop`-valued structure with the three fields `samplerProg`, `deciderProg` and `dim`; the programs enter as data because `Prog` is not a `Primcodable` type. `REPred` is Mathlib's, on the `Primcodable` product $\alpha \times \mathbb N$. The docstring records the organisation: `Verifier.not_isBounded_iff_exists` turns the negation into a search for a witness, `Verifier.boundViolationB` is the decidable test (the two time bounds through `Machine.haltsWithinB`, which needs the cost of a run), and `REPred.of_computable_exists` does the searching.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Semidecider.lean#L376-L454; blueprint lem:bounded-violation-re

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
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
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
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
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
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
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider

open MIPRE
open MIPRE.Verifier
open MIPRE.Cost
open HaltingGameValue (GameData)

theorem MIPRE.Verifier.rePred_not_isBounded {α : Type*} [Primcodable α] {ℓ : ℕ} {V : α → Verifier ℓ}
    (hV : ComputablyPresented V) :
    REPred fun q : α × ℕ => ¬ (V q.1).IsBounded q.2 := by sorry
