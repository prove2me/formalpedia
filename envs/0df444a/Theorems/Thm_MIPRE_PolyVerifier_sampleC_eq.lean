-- Prove2me | Theorems.Thm_MIPRE_PolyVerifier_sampleC_eq
-- name    : MIPRE.PolyVerifier.sampleC_eq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:24:56.715084+00:00
-- url     : https://prove2.me/theorems/bf7c41fc-fe4f-4f12-9548-909b1c3f3591
-- title:
--   The budgeted run of a polynomial-time verifier's sampler returns its question pair
-- statement:
--   Let $V$ be a polynomial-time verifier (`PolyVerifier`): a closed sampler program, a closed decider program and a polynomial $P \in \mathbb{N}[X]$, with $B(z) = P(|z|)$ for an input string $z$. The sampler is run on the encoding of the pair $(z, r)$ for a seed $r$. The budgeted sample `sampleC sd T z r` runs the program encoded by the datum `sd` on `encode (z, r)` under the cost budget $T$ with the computable evaluator `Machine.runForD`, decodes the result as a pair of bit strings, and returns $([], [])$ if the run does not finish within the budget or its result is not a pair of strings. The question pair `V.questions z r` is the sampler's output when it halts on `encode (z, r)` with a pair of strings of length at most $B(z)$, and the pair of empty strings otherwise; its components are elements of `Answers (V.B z)`, the strings of length at most $B(z)$.
--
--   Assume `V.Efficient z`: on every seed of length $B(z)$ the sampler halts within cost $P(|z| + |r|)$ with a pair of strings of length at most $B(z)$, the decider halts within cost $P(|z| + |x| + |y| + |a| + |b|)$ on every input $(z, x, y, a, b)$, and the decider rejects whenever one of $x, y, a, b$ is longer than $B(z)$. Assume also that $r$ is a seed of length exactly $B(z)$. Then
--
--   $$\mathrm{sampleC}\ (\mathrm{encode}\ V.\mathrm{sampler})\ \big(P(|z| + B(z))\big)\ z\ r \;=\; \big((V.\mathrm{questions}\ z\ r)_1,\ (V.\mathrm{questions}\ z\ r)_2\big),$$
--
--   the right-hand side being the pair of underlying bit strings of the two answers.
--
--   This is the identification of the computable table of the game $G_z$ with its question distribution: the tabulation `tabOf` builds the question weights of the table from `sampleC` at exactly this budget, and the lemma is what `mu_clause`, hence `quantumValue_tab` and the inclusion of the paper's class in the computable one (`MIPStar.toComputable`), rest on.
--
--   **Formalization Note** `sampleC` is total: `Machine.runForD` iterates the machine's step function $3T$ times and returns `none` when the configuration reached is not final, and both that case and a decoding failure give the junk value `([], [])`. The budget is written `V.bound.eval (z.length + V.B z)`, which is $P(|z| + |r|)$ with $|r| = B(z)$. `V.questions` has the fallback `(emptyAnswer, emptyAnswer)`; the statement says that under the hypotheses it is not taken. The arguments `z` and `r` are implicit, `V` is a section variable, and the proposition is `MIPRE.PolyVerifier.sampleC_eq`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ClassMIPStarTab.lean#L379-L395

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
import Definitions.Def_MIPRE_Foundations_ClassMIPStar
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_ClassMIPStarTab

open MIPRE
open MIPRE.PolyVerifier
open MIPRE.Cost MIPRE.Verifier
open HaltingGameValue (GameData)
variable (V : PolyVerifier)

theorem MIPRE.PolyVerifier.sampleC_eq {z : BitStr} (h : V.Efficient z) {r : BitStr} (hr : r.length = V.B z) :
    sampleC (encode V.sampler) (V.bound.eval (z.length + V.B z)) z r =
      ((V.questions z r).1.1, (V.questions z r).2.1) := by sorry
