-- Prove2me | Theorems.Thm_MIPRE_Halting_exists_compressorSpec
-- name    : MIPRE.Halting.exists_compressorSpec
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:31:08.562068+00:00
-- url     : https://prove2.me/theorems/c7af755d-06de-4615-b17d-481d56888f69
-- title:
--   The compressor meets its specification: a polynomial-time program for $(c, n) \mapsto \mathrm{comprStr}(c, n, \lambda(n))$ yields a CompressorSpec
-- statement:
--   Fix $G$ (`GapCompression`, with constant $C_0$, compressed samplers, output verifiers `G.output` and polynomial $\mathrm{bound}$) and $U$ (`UniversalMachine`); write $|a|$ for `esize a`. `CompressorSpec G U` is the specification of the compressor of the halting reduction: a threshold $n_0 \ge C_0$; a polynomial-time function `compr : PolyTimeFun (Prog × ℕ) BitStr` (a function with a closed program computing it on encodings and an explicit polynomial cost bound); a parameter `lam : ℕ → ℕ`; and five properties, all for $n \ge n_0$. `descLam_compr`: `compr (c, n)` carries the parameter `lam n`. `accepts_compr`: for $2|c| \le n$, $(c, n)$ a succinct description of $x$ and $|x| \le n+1$, the decider of `Vof (compr (c, n))` accepts, at every index and on all questions and answers, exactly what the compressed decider `G.output` of the verifier of $x$ frozen at index $2n+1$, at parameter `lam n`, accepts. `isBounded_compr`: under the same hypotheses, if `Vof x` is $(2n+1)$-bounded then `Vof (compr (c, n))` is $n$-bounded. `lam_ge`: $(2n+1)^{2n+1} + |2n+1| + 4 \le 2^{\mathrm{lam}\,n}$ and $2n+1 + |2n+1| + 53 \le \mathrm{lam}\,n$. `ansBound_le`: for $|x| \le n+1$, $\mathrm{ansBound}(x, 2n+1) \le (2^n)^{\mathrm{lam}\,n}$. Let `compr` be a polynomial-time function with $\mathrm{compr}(c, n) = \mathrm{comprStr}(c, n, \lambda(n))$ for all $c, n$, where $\lambda(n) = 2^{2\,\mathrm{size}(n)}$ and `comprStr G U c n lam` is the string denoting the parameter `lam` and the decider `haltProg G U` with $(c, n, \mathrm{lam})$ hardcoded. Then
--
--   $$ \exists\, S : \mathrm{CompressorSpec}(G, U):\qquad S.\mathrm{compr} = \mathrm{compr}\ \ \wedge\ \ S.\mathrm{lam} = \lambda. $$
--
--   A `CompressorSpec` yields `Obligations G U` by the class transfer `CompressorSpec.toObligations`, and `Obligations` is all the halting reduction assumes beyond a gap compression and a universal machine; the program itself (`comprPoly` of `Halting/CompressorProgram.lean`) supplies the hypothesis.
--
--   **Formalization Note** The statement is `MIPRE.Halting.exists_compressorSpec`, with `G`, `U`, `compr` and `hcompr : ∀ c n, compr (c, n) = comprStr G U c n (lamOf n)` explicit; `compr (c, n)` is the `PolyTimeFun` coerced to its underlying function. The conclusion fixes the two data fields `compr` and `lam = lamOf` of the witness and leaves its threshold `n₀` existential.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/CompressorCost.lean#L508-L530; blueprint lem:lambda, https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Halting.exists_compressorSpec (compr : PolyTimeFun (Prog × ℕ) BitStr)
    (hcompr : ∀ (c : Prog) (n : ℕ), compr (c, n) = comprStr G U c n (lamOf n)) :
    ∃ S : CompressorSpec G U, S.compr = compr ∧ S.lam = lamOf := by sorry
