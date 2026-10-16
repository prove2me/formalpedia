-- Prove2me | Theorems.Thm_MIPRE_Halting_seedCount_eq
-- name    : MIPRE.Halting.seedCount_eq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:35:21.086725+00:00
-- url     : https://prove2.me/theorems/a4dbbaa5-fb7e-4365-bc4f-b9a7225a0815
-- title:
--   Seeds of the class verifier producing a given question pair: a count over $\mathbb F_2^{s(C)}$ times $2^{B(z) - s(C)}$
-- statement:
--   Fix a gap-preserving compression instance $G$, a universal machine $U$, a clocked universal machine $U_T$, naturals $\Lambda_0, K$ and a polynomial-time map $R$ from bit strings to programs, and let $\mathcal V^{\mathrm{cl}} = \mathrm{classV}(G, U, U_T, \Lambda_0, K, R)$ be the class verifier with bound $B(z)$. On an input $z$ it plays the halting verifier $\mathcal W_z = \mathcal V^{\mathrm{halt}}_{R(z), \lambda(z)}$, $\lambda(z) = \Lambda_0 + 4|R(z)|$, whose sampler is the compressed sampler $S^{\mathrm{compr}}_{\lambda(z)}$; at the fixed level $C_G$ this sampler has dimension $s = s(C_G)$ and two conditionally linear functions $L^{\mathsf A}, L^{\mathsf B} : \mathbb F_2^{s} \to \mathbb F_2^{s}$, one per player. The questions of $\mathcal W_z$ at level $C_G$ are the vectors of $\mathbb F_2^{s}$, and $\iota$ (`qEmb`) embeds them into the strings of length at most $B(z)$ by listing their coordinates. The seed count $\mathrm{seedCount}_z(x', y')$ is the number of seeds $r \in \{0,1\}^{B(z)}$ for which the sampler's output on $\mathrm{encode}(z, r)$, read as a pair of strings of length at most $B(z)$, is $(x', y')$.
--
--   For all $x, y \in \mathbb F_2^{s}$,
--
--   $$ \mathrm{seedCount}_z(\iota x, \iota y) \;=\; \#\bigl\{ v \in \mathbb F_2^{s} :\ L^{\mathsf A}(v) = x \ \wedge\ L^{\mathsf B}(v) = y \bigr\} \cdot 2^{\,B(z) - s}. $$
--
--   The seed count is the numerator of the question distribution of the game $G_z$ of the class verifier, $\mu_{G_z}(x', y') = \mathrm{seedCount}_z(x', y') / 2^{B(z)}$; dividing, `classV_game_mu` identifies $\mu_{G_z}$ on the embedded questions with the compressed sampler's distribution.
--
--   **Formalization Note**. The statement is `MIPRE.Halting.seedCount_eq`, with `G U UT Λ₀ K R` as section variables. `(Vz G U UT Λ₀ R z).Questions (C G)` is `Fin (dimz G Λ₀ R z) → ZMod 2`, the count is `(Finset.univ.filter …).card` over it, and the two conditions are `((Vz …).sampler.cl (C G) .alice).eval v = x` and the same for `.bob`. `qEmb G U UT Λ₀ K R z` is an embedding into `Answers ((classV …).B z)` with `(qEmb … v).1 = CL.toBits v`, and `seedCount` is `PolyVerifier.seedCount`, the length of a filtered enumeration `Data.bitStrsOfLen (B z)`. The exponent `(classV …).B z - dimz G Λ₀ R z` is natural-number subtraction; the module proves `dimz_le_B`, so it is not truncated.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/ClassMain.lean#L228-L269; internal lemma for blueprint thm:halting at the fixed level (module docstring); no blueprint label is attached to this declaration

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
import Mathlib.Data.Nat.Log
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
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_ManyOne
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_LambdaBound
import Definitions.Def_MIPRE_Foundations_Halting_Absorb
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor
import Definitions.Def_MIPRE_Foundations_Halting_Paper_TabulateL
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Decider
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Size
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Cost
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Induction
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Stages
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Build
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Main
import Definitions.Def_MIPRE_Foundations_Halting_Paper_ClassVerifier
import Definitions.Def_MIPRE_Foundations_Halting_Paper_ClassMain

open MIPRE
open MIPRE.Halting
open MIPRE.Cost MIPRE.Cost.Prog MIPRE.Cost.PolyTimeFun MIPRE.CL MIPRE.Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)

theorem MIPRE.Halting.seedCount_eq (z : BitStr) (x y : (Vz G U UT Λ₀ R z).Questions (C G)) :
    (classV G U UT Λ₀ K R).seedCount z (qEmb G U UT Λ₀ K R z x) (qEmb G U UT Λ₀ K R z y) =
      (Finset.univ.filter fun v : (Vz G U UT Λ₀ R z).Questions (C G) =>
        ((Vz G U UT Λ₀ R z).sampler.cl (C G) .alice).eval v = x ∧
          ((Vz G U UT Λ₀ R z).sampler.cl (C G) .bob).eval v = y).card *
        2 ^ ((classV G U UT Λ₀ K R).B z - dimz G Λ₀ R z) := by sorry
