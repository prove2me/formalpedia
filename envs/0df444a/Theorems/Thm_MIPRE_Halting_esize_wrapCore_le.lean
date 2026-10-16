-- Prove2me | Theorems.Thm_MIPRE_Halting_esize_wrapCore_le
-- name    : MIPRE.Halting.esize_wrapCore_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:27:58.692995+00:00
-- url     : https://prove2.me/theorems/26b501b5-3432-4adc-8168-fef327811db5
-- title:
--   Size of the compressor's output decider: at most the description size plus a polynomial in the binary length of the level
-- statement:
--   Fix a gap-preserving compression instance $G$ (`GapCompression`), whose compressed sampler at parameter $\lambda$ is $S^{\mathrm{compr}}_\lambda$ with program computed by the polynomial-time function `G.samplerProg`, and a universal machine $U$ with program `U.univ`. Sizes are node counts of tree encodings: $|a|$ denotes `esize a`, the number of nodes of `encode a`, and $\mathrm{size}(n)$ is the binary length of $n$ (Mathlib's `Nat.size`). At level $n$ the compressor's output carries the parameter $\lambda(n) = 2^{2\,\mathrm{size}(n)}$ and the decider program $\mathrm{outDec}(c, n, \lambda(n))$: the compressor's decider `haltProg G U` with the triple $(c, n, \lambda(n))$ hardcoded. The decider of the verifier this output denotes is the wrapper $\mathrm{wrapCore}(U.\mathrm{univ}, \mathrm{prog}(S^{\mathrm{compr}}_{\lambda(n)}), \mathrm{encode}(\mathrm{outDec}(c, n, \lambda(n))))$, which on an input $(N, x, y, a, b)$ computes the sampler's dimension at $N$ through $U$, checks that $x$ and $y$ have that length, and runs the decider datum on the whole input through $U$, rejecting otherwise. Let $\mathrm{sizeZ}(s) = \mathrm{tb}(8s+5) + 12s + |\mathrm{haltProg}| + 2\,|U.\mathrm{univ}| + \mathrm{wrapNodes} + 43$, where $\mathrm{tb}$ is the polynomial cost bound of `G.samplerProg` and $\mathrm{wrapNodes}$ the fixed node count of the wrapper's skeleton. For every program $c$ and every $n \in \mathbb{N}$,
--
--   $$ \bigl|\mathrm{wrapCore}\bigl(U.\mathrm{univ},\ \mathrm{prog}(S^{\mathrm{compr}}_{\lambda(n)}),\ \mathrm{encode}(\mathrm{outDec}(c, n, \lambda(n)))\bigr)\bigr| \;\le\; |c| + \mathrm{sizeZ}(\mathrm{size}(n)). $$
--
--   This is the decider half of the size clause of the output's $n$-boundedness (`Verifier.IsBounded`): beyond the description $c$ it carries, the output's decider has size polynomial in $\log n$, and the slack $2|c| \le n$ of the compressibility criterion is what leaves room for $|c|$.
--
--   **Formalization Note** The statement is `MIPRE.Halting.esize_wrapCore_le`, with `G : GapCompression` and `U : UniversalMachine` explicit and no hypothesis on `c` or `n`. `lamOf n` unfolds to `2 ^ (2 * Nat.size n)`, `outDec G U c n lam` to `hardcode (haltProg G U) (encode (c, n, lam))`, and `sizeZ G U s` to `G.samplerProg.timeBound.eval (8 * s + 5) + 12 * s + (esize (haltProg G U) + 2 * esize U.univ + wrapNodes + 43)`. The bound is on the raw wrapper program `Prog.wrapCore`, not on the `Verifier` built from it.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/CompressorCost.lean#L131-L148; internal lemma of the formalization of blueprint thm:halting (obligation O4 of rem:compression-abstract, the accounting of the compressor's output), https://vidick.github.io/MIPRE-formalization/blueprint/

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
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
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
import Definitions.Def_MIPRE_Foundations_Halting_CompressorCost

open MIPRE
open MIPRE.Halting
open MIPRE.Cost MIPRE.Cost.Prog MIPRE.Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)

theorem MIPRE.Halting.esize_wrapCore_le (c : Prog) (n : ℕ) :
    esize (wrapCore U.univ (G.sampler (lamOf n)).prog (encode (outDec G U c n (lamOf n)))) ≤
      esize c + sizeZ G U (Nat.size n) := by sorry
