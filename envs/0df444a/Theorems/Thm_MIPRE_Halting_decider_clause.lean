-- Prove2me | Theorems.Thm_MIPRE_Halting_decider_clause
-- name    : MIPRE.Halting.decider_clause
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:29:44.386795+00:00
-- url     : https://prove2.me/theorems/600650b9-d89c-4a1f-ad0e-0463dfce0ca5
-- title:
--   Decider clause of the compressor's output: past a threshold, the output's decider runs within $m^n (|d|+1)^n$ at every index $m \ge 2$
-- statement:
--   Fix $G$ (`GapCompression`) and $U$ (`UniversalMachine`), and write $|a|$ for `esize a` (the node count of the encoding) and $\mathrm{size}(k)$ for the binary length of $k$. On $(c, n)$ the compressor outputs the string $\mathrm{comprStr}(c, n, \lambda(n))$: the postorder serialization of the pair of the parameter $\lambda(n) = 2^{2\,\mathrm{size}(n)}$ and the decider program $\mathrm{outDec}(c, n, \lambda(n))$, the compressor's decider `haltProg G U` with $(c, n, \lambda(n))$ hardcoded. A string $y$ denotes the verifier $\mathrm{Vof}(y)$: the compressed sampler at the parameter the string carries, and the string's decider datum run by $U$ inside the question-length wrapper (`Decider.wrap`). For a decider $\mathcal{D}$, `TimeBoundAt m T k` says that for every datum $d$ the program of $\mathcal{D}$ halts on the input $\mathrm{cons}(\mathrm{encode}\,m, d)$ within cost $T(|d|+1)^k$. The pair $(c, n)$ is a succinct description of $x$ (`IsSuccinctDesc c n x`) when $c$ is closed, $|x| \le 2^n$ and $c$ answers every bit query $k$ about $x$ within cost $(n+1)(\mathrm{size}(k)+1)^2$. There is a threshold $n_0$, depending on $G$ and $U$ alone, such that for all $n \ge n_0$, all programs $c$ and bit strings $x$ with $2|c| \le n$, $(c, n)$ a succinct description of $x$ and $|x| \le n+1$, and every index $m \ge 2$:
--
--   $$ \forall d \in \mathrm{Data}:\qquad \text{the decider of } \mathrm{Vof}\bigl(\mathrm{comprStr}(c, n, \lambda(n))\bigr) \text{ halts on } \mathrm{cons}(\mathrm{encode}\,m,\ d) \text{ within cost } m^{n}\,(|d|+1)^{n}. $$
--
--   This is the decider clause of `Verifier.IsBounded n` for the output's verifier, the third of its per-index clauses (dimension, sampler time, decider time); with the sampler and size clauses it yields the field `CompressorSpec.isBounded_compr`, the accounting half of obligation O4.
--
--   **Formalization Note** The statement is `MIPRE.Halting.decider_clause`, with `G`, `U` explicit. The conclusion `(Vof G U (comprStr G U c n (lamOf n))).decider.TimeBoundAt m (m ^ n) n` unfolds to `∀ d : Data, HaltsWithin prog (.cons (encode m) d) (m ^ n * (d.size + 1) ^ n)`, with `HaltsWithin p x t := ∃ r t', t' ≤ t ∧ Eval [x] p r t'`: `d` ranges over all data, well formed or not, and nothing is said about the result. The threshold is existential; `2 * esize c ≤ n` and `x.length ≤ n + 1` are the slack and the length bound the compressibility criterion provides; the bound is in `m` and `n`, not in `λ(n)`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/CompressorCost.lean#L426-L443; internal lemma of the formalization of blueprint thm:halting (obligation O4 of rem:compression-abstract, the accounting of the compressor's output), https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Halting.decider_clause : ∃ n₀, ∀ n, n₀ ≤ n → ∀ (c : Prog) (x : BitStr), 2 * esize c ≤ n →
    IsSuccinctDesc c n x → x.length ≤ n + 1 → ∀ m, 2 ≤ m →
    (Vof G U (comprStr G U c n (lamOf n))).decider.TimeBoundAt m (m ^ n) n := by sorry
