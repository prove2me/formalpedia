-- Prove2me | Theorems.Thm_MIPRE_Halting_sampProg_runs
-- name    : MIPRE.Halting.sampProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:35:24.030378+00:00
-- url     : https://prove2.me/theorems/256a3445-04ff-4c9d-b30e-3613701b7d59
-- title:
--   The class verifier's sampler halts with the halting verifier's question pair within the explicit cost bound
-- statement:
--   Fix a gap-preserving compression instance $G$, a universal machine $U$, a natural number $\Lambda_0$ and a polynomial-time map $R$ from bit strings to programs. For an input $z$ write $M = R(z)$, $\lambda(z) = \Lambda_0 + 4|M|$ ($|M|$ the size of the encoding of $M$), $S_z = S^{\mathrm{compr}}_{\lambda(z)}$ for the compressed sampler at this parameter, $s = s(C_G)$ for its dimension at the fixed level $C_G = \max(C_0, 2)$, and $L^{\mathsf A}, L^{\mathsf B} : \mathbb F_2^{s} \to \mathbb F_2^{s}$ for its two conditionally linear functions at that level. The question of player $w$ on the seed $r$ is $q_w(z, r) = \mathrm{bits}\bigl(L^{w}(\mathrm{vec}_s(r_{< s}))\bigr)$: the vector of $\mathbb F_2^{s}$ read off the first $s$ bits of $r$ (missing bits read as $0$), mapped by $L^{w}$, listed as a bit string. The sampler $\mathrm{sampProg}$ of the class verifier computes $M$, $\lambda(z)$ and the program of $S_z$, asks $S_z$ its dimension through $U$, converts it to unary, and asks Alice's and then Bob's marginal at the first $s$ bits of the seed through $U$. $\mathrm{sampB}(m)$ is the module's explicit cost expression in the total input length $m$, assembled from the time polynomials of the three stage functions, the overhead polynomial of $U$, $\mathrm{bound}_G$ and the time polynomial of $R$, and polynomially bounded (`polyBounded_sampB`).
--
--   Let $z, r$ be bit strings with $s \le |r|$. Then
--
--   $$ \exists\, t \le \mathrm{sampB}(|z| + |r|):\qquad \mathrm{sampProg}\ \text{on the input}\ \mathrm{encode}(z, r)\ \text{halts with}\ \mathrm{encode}\bigl(q_{\mathsf A}(z, r),\ q_{\mathsf B}(z, r)\bigr)\ \text{at cost}\ t. $$
--
--   This is the sampler clause of the efficiency of the class verifier (`classV_efficient`) and the determination of its question pair on every seed, from which the uniform seed of length $B(z) \ge s$ pushes forward to the compressed sampler's distribution (`seedCount_eq`, `classV_game_mu`).
--
--   **Formalization Note**. The statement is `MIPRE.Halting.sampProg_runs`, with `G U Λ₀ R` the section variables occurring in it. `Prog.Runs p x r t` is `Eval [x] p r t`; `qOf G Λ₀ R w z r` is `CL.toBits (((Sz G Λ₀ R z).cl (C G) w).eval (CL.ofBits (dimz G Λ₀ R z) (r.take (dimz G Λ₀ R z))))`; the hypothesis `hd : dimz G Λ₀ R z ≤ r.length` asks only that the seed be long enough, and the bound `sampB G U Λ₀ R (z.length + r.length)` is in the total input length, as `PolyVerifier.Efficient.sampler_runs` requires. The cost `t` is existential.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/ClassVerifier.lean#L184-L351; blueprint thm:halting

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

open MIPRE
open MIPRE.Halting
open MIPRE.Cost MIPRE.Cost.Prog MIPRE.Cost.PolyTimeFun MIPRE.CL
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)

theorem MIPRE.Halting.sampProg_runs (z r : BitStr) (hd : dimz G Λ₀ R z ≤ r.length) :
    ∃ t, t ≤ sampB G U Λ₀ R (z.length + r.length) ∧
      (sampProg G U Λ₀ R).Runs (encode (z, r))
        (encode (qOf G Λ₀ R .alice z r, qOf G Λ₀ R .bob z r)) t := by sorry
