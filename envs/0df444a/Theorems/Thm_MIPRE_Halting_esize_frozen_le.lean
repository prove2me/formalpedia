-- Prove2me | Theorems.Thm_MIPRE_Halting_esize_frozen_le
-- name    : MIPRE.Halting.esize_frozen_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:28:28.532259+00:00
-- url     : https://prove2.me/theorems/a452bb3e-44df-4b92-aebf-525589fcd2d3
-- title:
--   The two frozen programs of a described verifier fit under the size bound of the compressor's accounting
-- statement:
--   Let $G$ be a gap-preserving compression (`GapCompression`: a compressed sampler family `G.sampler : ℕ → CL.Sampler 7`, a polynomial-time `G.samplerProg : PolyTimeFun ℕ Prog` computing its program from the parameter, the compression map `G.compress : PolyTimeFun ((Prog × Prog) × ℕ) Prog`, the bounds, and the completeness and soundness guarantees), and $U$ an efficient universal machine. For a bit string $x$, `Vof G U x : Verifier 7` is the verifier $x$ denotes: the compressed sampler at the parameter `descLam x` the string denotes and the decider datum `descDecD x` it denotes, wrapped in the question-length check (`Verifier.ofSamplerDeciderD`). `frozen G U x n = (Vof G U x).freeze (2n + 1)` is that verifier frozen at index $2n + 1$: its sampler and decider programs are `freezeProg (2n + 1)` of the originals, which on an input `cons N d` run the original on `cons (encode (2n + 1)) d`. `esize p = (encode p).size` is the size of a program as data. The bound is $\mathrm{fBound}\ G\ U\ L\ n = \mathrm{sampBound}\ G\ L + \mathrm{kBound}\ n + 53 + (\mathrm{wBound}\ G\ U\ L + \mathrm{kBound}\ n + 53)$, with $\mathrm{sampBound}\ G\ L$ the evaluation of the time-bound polynomial of `G.samplerProg` at $L + 1$, $\mathrm{kBound}\ n = 4\,\mathrm{size}\ n + 5$ (with $\mathrm{size}\ n$ the binary length `Nat.size n`), and $\mathrm{wBound}\ G\ U\ L = \mathrm{sampBound}\ G\ L + (L + 1) + 2\,\mathrm{esize}\ U.\mathrm{univ} + \mathrm{wrapNodes}$, where `wrapNodes` is the constant node count of the wrapped decider's description. Then for every bit string $x$ and every $n$,
--
--   $$\mathrm{esize}\ (\mathrm{frozen}\ G\ U\ x\ n).\mathrm{sampler.prog} + \mathrm{esize}\ (\mathrm{frozen}\ G\ U\ x\ n).\mathrm{decider.prog} \;\le\; \mathrm{fBound}\ G\ U\ |x|\ n .$$
--
--   The pair of frozen programs is the input handed to `G.compress` in the last stage of the compressor's preparation `prepProg`; this bound on its size is what `prepBound` passes through `G.compress.timeBound`, and `prepProg_runs` and the cost accounting of the decider use it.
--
--   **Formalization Note** The bound depends on $x$ only through its length `x.length`, and no hypothesis is made on $x$: every string denotes a verifier, well formed or not. `fBound` is noncomputable only through the evaluation of the polynomial `G.samplerProg.timeBound`. `G` and `U` are section variables and `x`, `n` explicit arguments; the proposition is `MIPRE.Halting.esize_frozen_le`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Compressor.lean#L607-L621; paper recursive.tex, fig:halt_f (the compressor's decider is the paper's machine 𝓕 with the recursion removed)

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
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor

open MIPRE
open MIPRE.Halting
open MIPRE.Cost
open MIPRE.Cost MIPRE.Cost.Prog MIPRE.Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)

theorem MIPRE.Halting.esize_frozen_le (x : BitStr) (n : ℕ) :
    esize (frozen G U x n).sampler.prog + esize (frozen G U x n).decider.prog ≤
      fBound G U x.length n := by sorry
