-- Prove2me | Theorems.Thm_MIPRE_Halting_outDec_cost
-- name    : MIPRE.Halting.outDec_cost
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:44:07.244789+00:00
-- url     : https://prove2.me/theorems/5018da1d-0dd1-404d-9a14-078517a10a58
-- title:
--   Cost of the compressor's inner decider on a succinct description: the explicit bound innerBound
-- statement:
--   Fix $G$ (`GapCompression`, with polynomial $\mathrm{bound}$, degree $\deg$ and compression map `G.compress`) and $U$ (`UniversalMachine`, with overhead polynomial $U.\mathrm{bound}$); write $|a|$ for `esize a`, the node count of the encoding of $a$, and $\mathrm{size}(k)$ for the binary length of $k$. The pair $(c, n)$ is a succinct description of the bit string $x$ (`IsSuccinctDesc c n x`) when $c$ is a closed program, $|x| \le 2^n$, and for every $k \in \mathbb{N}$ the program $c$ on the binary input $k$ returns the bit-query answer about $x$ within cost $(n+1)(\mathrm{size}(k)+1)^2$. The inner decider $\mathrm{outDec}(c, n, \lambda)$ is the compressor's decider `haltProg G U` with $(c, n, \lambda)$ hardcoded. `innerBound G U s n L λ l m t` is the explicit natural number $3\,\mathrm{prepBound}(s, n, L, l) + 2(s + 4\,\mathrm{size}(n) + 1 + l + 2) + 3(4\,\mathrm{size}(m) + 1 + t + 1) + U.\mathrm{bound}\bigl(\mathrm{tb}_{\mathrm{compress}}(\mathrm{fBound}(L, n) + l + 2) + (4\,\mathrm{size}(m) + 1 + t + 1) + \mathrm{bound}(m + \lambda)\,(t+1)^{\deg}\bigr) + 15$, where `prepBound` bounds the preparation, $\mathrm{tb}_{\mathrm{compress}}$ is the cost polynomial of `G.compress` and `fBound` bounds the sizes of the frozen programs. For every succinct description $(c, n)$ of $x$, every $\lambda, m \in \mathbb{N}$ and every datum $d$, there exist a result $r$ and a cost $t$ with
--
--   $$ t \;\le\; \mathrm{innerBound}\bigl(|c|,\ n,\ |x|,\ \lambda,\ |\lambda|,\ m,\ |d|\bigr) \quad\text{and}\quad \mathrm{outDec}(c, n, \lambda)\ \text{on the input}\ \mathrm{cons}(\mathrm{encode}\,m,\ d)\ \text{halts with result}\ r\ \text{at cost}\ t. $$
--
--   Per its docstring, the bound is the compressed decider's own time (`GapCompression.decider_time`), simulated by the universal machine, after the preparation; it is the inner cost the wrapper's cost `wrapCoreCost` takes as a parameter.
--
--   **Formalization Note** The statement is `MIPRE.Halting.outDec_cost`, with `G`, `U` explicit, `c x n` implicit and `hsd : IsSuccinctDesc c n x`; `(outDec G U c n lam).Runs (.cons (encode m) d) r t` means `Eval [cons (encode m) d] (outDec G U c n lam) r t`, a terminating run with result `r` at cost `t`. The result `r` is existential and unconstrained: a halting-and-cost statement only. `d : Data` is arbitrary, `d.size` its node count. The numerals `m` and `n` enter `innerBound` through `4 * Nat.size _ + 1`, the general bound on the `esize` of a natural, which keeps the bound monotone.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/CompressorCost.lean#L180-L209; internal lemma of the formalization of blueprint thm:halting (obligation O4 of rem:compression-abstract, the accounting of the compressor's output), https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Halting.outDec_cost {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x) (lam m : ℕ)
    (d : Data) :
    ∃ r t, t ≤ innerBound G U (esize c) n x.length lam (esize lam) m d.size ∧
      (outDec G U c n lam).Runs (.cons (encode m) d) r t := by sorry
