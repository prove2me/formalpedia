-- Prove2me | Theorems.Thm_MIPRE_Halting_exists_ansBound_le
-- name    : MIPRE.Halting.exists_ansBound_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:32:49.379673+00:00
-- url     : https://prove2.me/theorems/295b87e8-6022-43fe-ba0b-e89373769593
-- title:
--   The answer budget of level 2n+1 fits under the compression theorem's budget $(2^n)^\lambda$, for short strings and large parameters
-- statement:
--   Fix a gap-preserving compression instance $G$ (`GapCompression`), with the polynomial $\mathrm{bound} \in \mathbb{N}[X]$ that bounds the running times of its outputs and the length of the answers its compressed deciders accept: at index $n$ and parameter $\lambda$ the compressed decider accepts no answer longer than $\mathrm{bound}(n + \lambda)$. A bit string $x$ denotes a description: it parses (`Data.parse`, the postorder stack machine) to a datum whose left component, normalized to a canonical binary numeral, is the parameter $\lambda_x = \mathrm{descLam}(x) \in \mathbb{N}$ the string carries; every string carries one. The answer budget the classes of the halting reduction are read with at level $n$ is $\mathrm{ansBound}(x, n) = \mathrm{bound}(n + \lambda_x)$. There are thresholds $\lambda_0, n_0 \in \mathbb{N}$, depending on $G$ alone, such that for every bit string $x$ and all $\lambda, n$ with $\lambda \ge \lambda_0$, $n \ge n_0$ and $|x| \le n + 1$,
--
--   $$ \mathrm{ansBound}(x,\ 2n+1) \;=\; \mathrm{bound}\bigl(2n + 1 + \lambda_x\bigr) \;\le\; \bigl(2^{n}\bigr)^{\lambda}. $$
--
--   Per its docstring, $(2^n)^\lambda$ is the answer bound at which `GapCompression.completeness` takes its hypothesis, so this inequality (with `Verifier.hasPerfectPCC_of_le`) carries a value-$1$ PCC strategy from membership in the class $A$ at level $2n+1$ into that clause; it is why `Obligations.compr_spec` carries the length bound $|x| \le n+1$: the budget grows with the string's own parameter, and without a bound on it no thresholds would do. The docstring records the witnesses $\lambda_0 = 2\deg(\mathrm{bound}) + 1$ and $n_0 = \log_2\|\mathrm{bound}\| + 2\deg(\mathrm{bound}) + 1$, with $\|\mathrm{bound}\|$ the sum of the coefficients; they are set by the polynomial, not by `G.deg`.
--
--   **Formalization Note** The statement is `MIPRE.Halting.exists_ansBound_le`, with `G : GapCompression` explicit and no universal machine involved. `ansBound G x n` unfolds to `G.bound.eval (n + descLam x)` and `descLam x` to `Data.natOf (Data.parse x).left`, both total on arbitrary strings; `(2 ^ n) ^ lam` is in ℕ. The thresholds are existential in the statement; the explicit values above are the docstring's. The field `CompressorSpec.ansBound_le` is this statement at `lam = lamOf n` with a single threshold.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Instantiation.lean#L155-L194; internal lemma of the formalization of blueprint thm:halting (the answer budget of the classes of rem:compression-abstract, behind the field ansBound_le of the compressor's specification), https://vidick.github.io/MIPRE-formalization/blueprint/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
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
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
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
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation

open MIPRE
open MIPRE.Halting
open MIPRE.Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)

theorem MIPRE.Halting.exists_ansBound_le (G : GapCompression) :
    ∃ lam₀ n₀ : ℕ, ∀ (x : BitStr) (lam n : ℕ), lam₀ ≤ lam → n₀ ≤ n → x.length ≤ n + 1 →
      ansBound G x (2 * n + 1) ≤ (2 ^ n) ^ lam := by sorry
