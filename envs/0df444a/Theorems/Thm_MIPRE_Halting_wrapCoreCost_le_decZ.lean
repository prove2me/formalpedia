-- Prove2me | Theorems.Thm_MIPRE_Halting_wrapCoreCost_le_decZ
-- name    : MIPRE.Halting.wrapCoreCost_le_decZ
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:30:16.089116+00:00
-- url     : https://prove2.me/theorems/2d3c8cf0-b395-4444-9782-22293d38883e
-- title:
--   The output decider's wrapper cost is below the master bound decZ at the largest of the index, the level and the input size
-- statement:
--   Fix $G$ (`GapCompression`, with polynomial $\mathrm{bound}$ and degree $\deg$) and $U$ (`UniversalMachine`, with overhead polynomial $U.\mathrm{bound}$); write $|a|$ for `esize a`, $\mathrm{size}(z)$ for the binary length of $z$ and $\lambda(n) = 2^{2\,\mathrm{size}(n)}$. `wrapCoreCost U S dec Cf kf m T s` is the cost of the wrapper `wrapCore` around the decider program `dec` at index $m$ on an input of size $s$, when `dec` runs within $T$ on it and `S` runs within $Cf(m')(|d|+1)^{kf}$ at index $m'$: $(60\,\mathrm{wrapHeadZ}^2 + 4) + 2\,\mathrm{checkCost}(s, \dim_S(m)) + 2(|\mathrm{dec}| + |m| + s + 2) + U.\mathrm{bound}(|\mathrm{dec}| + |m| + s + 1 + T) + 20$, with $\mathrm{checkCost}(E, k) = 60(E + k + 30)^2$ and $\mathrm{wrapHeadZ}$ bounding the head that computes the sampler's dimension. `decZ G U z` is the master bound: the same expression with every atom replaced by its bound in the single variable $z$: the compressed sampler's program size $\sigma(z)$, the inner decider's size $\delta(z)$, the inner cost $\iota(z) = \mathrm{innerBound}(z, z, z+1, \lambda(z), 8\,\mathrm{size}(z)+5, z, z)$, the sampler bound $\mathrm{bound}(z + \lambda(z))$ and the head bound $\mathrm{headZ}(z)$. Let $c$ be a program, $x$ a bit string and $n, m, t, z \in \mathbb{N}$ with $|c| \le n$, $|x| \le n+1$, $m \le z$, $n \le z$ and $t \le z$. Then
--
--   $$ \mathrm{wrapCoreCost}\Bigl(U,\ S^{\mathrm{compr}}_{\lambda(n)},\ \mathrm{outDec}(c, n, \lambda(n)),\ m' \mapsto \mathrm{bound}(m' + \lambda(n)),\ \deg,\ m,\ \mathrm{innerBound}(|c|, n, |x|, \lambda(n), |\lambda(n)|, m, t),\ t\Bigr) \;\le\; \mathrm{decZ}(z). $$
--
--   The single variable is the point: the output decider's cost at index $m$, level $n$ and input size $t$ is dominated by one polynomially bounded function of $\max(m, n, t)$, the form the absorption lemmas of `Halting/Absorb.lean` turn into the clause $m^n (|d|+1)^n$ of $n$-boundedness.
--
--   **Formalization Note** The statement is `MIPRE.Halting.wrapCoreCost_le_decZ`, with `G`, `U` explicit and `c x n m t z` implicit, fixed by the hypotheses `hc hx hm hn ht`. No succinctness hypothesis and no run appear: both sides are closed arithmetic expressions over ℕ (`wrapCoreCost`, `innerBound`, `decZ` and its atoms `headZ`, `sampZ`, `sigZ`, `deltaZ`, `iotaZ` are definitions evaluating polynomials over ℕ). The sampler's coefficient function is the literal `fun m => G.bound.eval (m + lamOf n)` and its degree `G.deg`, the data of `GapCompression.sampler_time`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/CompressorCost.lean#L391-L424; internal lemma of the formalization of blueprint thm:halting (obligation O4 of rem:compression-abstract, the accounting of the compressor's output), https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Halting.wrapCoreCost_le_decZ {c : Prog} {x : BitStr} {n m t z : ℕ} (hc : esize c ≤ n)
    (hx : x.length ≤ n + 1) (hm : m ≤ z) (hn : n ≤ z) (ht : t ≤ z) :
    wrapCoreCost U (G.sampler (lamOf n)) (outDec G U c n (lamOf n))
        (fun m => G.bound.eval (m + lamOf n)) G.deg m
        (innerBound G U (esize c) n x.length (lamOf n) (esize (lamOf n)) m t) t ≤ decZ G U z := by sorry
