-- Prove2me | Theorems.Thm_MIPRE_Halting_halting_reduction_both_of
-- name    : MIPRE.Halting.halting_reduction_both_of
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:29:25.053899+00:00
-- url     : https://prove2.me/theorems/d4d791e2-5af1-4e99-bdb5-c6bce3de541e
-- title:
--   Halting reduction from gap-preserving compression, in both values: synchronous and quantum value 1 on halting machines, at most 1/2 otherwise
-- statement:
--   Computation is Mathlib's: a machine is a code $\mathcal{M}$ (`Nat.Partrec.Code`), halting on the empty input when $\mathcal{M}.\mathrm{eval}(0)$ is defined (`HaltsOnEmptyInput`), and maps are `Computable`. A game description $d$ (`GameData`), two naturals $n_X, n_A$ and two finite lists of natural-number weights on question pairs and of accepted tuples, denotes the synchronous game $d.\mathrm{toGame}$ on questions $\mathrm{Fin}(n_X+1)$ and answers $\mathrm{Fin}(n_A+1)$ whose distribution normalizes the weights (a point mass on $(0,0)$ when the total weight is $0$) and whose predicate accepts the listed tuples, unequal answers to equal questions always losing. $\mathrm{val}_{\mathrm{sync}}(d)$ (`gameValue d.toGame`) is the supremum over synchronous strategies (one projective measurement family for both players, measured in the tracial state $\mathrm{Tr}(\cdot)/\dim$) of the winning probability; $\mathrm{val}^*(d)$ (`quantumValue d.game`) is the supremum over finite-dimensional tensor-product strategies of the same game read as a two-player game. Assume a gap-preserving compression instance $G$ (`GapCompression`, blueprint `thm:compression`) and a universal machine $U$. Then there is one computable map $g$ from codes to game descriptions such that for every code $\mathcal{M}$:
--
--   $$ \bigl(\mathcal{M} \text{ halts on } \varepsilon \Rightarrow \mathrm{val}_{\mathrm{sync}}(g(\mathcal{M})) = 1 \wedge \mathrm{val}^*(g(\mathcal{M})) = 1\bigr) \ \wedge\ \bigl(\mathcal{M} \text{ does not halt on } \varepsilon \Rightarrow \mathrm{val}_{\mathrm{sync}}(g(\mathcal{M})) \le \tfrac12 \wedge \mathrm{val}^*(g(\mathcal{M})) \le \tfrac12\bigr). $$
--
--   The two headline statements, `halting_reduces_to_gameValue_of` (blueprint `thm:main`, synchronous value) and `halting_reduction_quantum_of` (`cor:main-quantum`, quantum value), are its two projections, on the same map.
--
--   **Formalization Note** The statement is `MIPRE.Halting.halting_reduction_both_of`, with `G : GapCompression` and `U : UniversalMachine` as explicit arguments (`include G U`): it is conditional on an instance of the compression theorem, which `MIPRE/MainTheorem.lean` supplies separately. `HaltsOnEmptyInput pc` unfolds to `(pc.eval 0).Dom`; `1 / 2` is the real one half; `GameData.game` is `d.toGame` repackaged as a `MIPRE.Game` with the same distribution and predicate; `Computable g` uses the `Primcodable` instance of `GameData` as a tuple. Only computability of `g` is claimed, no time bound.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/CompressorProgram.lean#L241-L278; blueprint thm:halting, https://vidick.github.io/MIPRE-formalization/blueprint/

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
import Definitions.Def_MIPRE_Foundations_Halting_CompressorProgram

open MIPRE
open MIPRE.Halting
open MIPRE.Cost
open MIPRE.Cost MIPRE.Cost.Prog
variable (G : GapCompression) (U : UniversalMachine)
include G U

theorem MIPRE.Halting.halting_reduction_both_of :
    ∃ g : Nat.Partrec.Code → HaltingGameValue.GameData, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        (HaltingGameValue.HaltsOnEmptyInput pc →
          HaltingGameValue.gameValue (g pc).toGame = 1 ∧ quantumValue (g pc).game = 1) ∧
        (¬ HaltingGameValue.HaltsOnEmptyInput pc →
          HaltingGameValue.gameValue (g pc).toGame ≤ 1 / 2 ∧ quantumValue (g pc).game ≤ 1 / 2) := by sorry
