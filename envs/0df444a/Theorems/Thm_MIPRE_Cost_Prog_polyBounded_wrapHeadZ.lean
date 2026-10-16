-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_polyBounded_wrapHeadZ
-- name    : MIPRE.Cost.Prog.polyBounded_wrapHeadZ
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:39:14.947059+00:00
-- url     : https://prove2.me/theorems/ea83d26e-6d0a-4c5a-bfd3-18303bea62be
-- title:
--   The head-cost quantity of the wrapper decider is polynomially bounded
-- statement:
--   Let $U$ be a universal machine of the ambient cost model (a closed program `U.univ` simulating any program, with overhead bounded by the polynomial `U.bound`) and let $S$ be an $\ell$-level sampler with program `S.prog` and dimension function $s(n) = $ `S.dim n`. For a cost coefficient function $C_f : \mathbb{N} \to \mathbb{N}$ and a degree $k_f$, `wrapHeadZ U S Cf kf n` is the following explicit natural number, where $q$ is the fixed datum encoding the sampler's `dimension` query, $|d|$ is the size of a datum, $\mathrm{esize}(x) = |\mathrm{encode}\ x|$, and $\mathrm{size}(m)$ is the bit length of $m$:
--
--   $$ Z(n) = \mathrm{esize}(S.\mathrm{prog}) + \mathrm{esize}(n) + |q| + \mathrm{esize}(s(n)) + C_f(n)(|q|+1)^{k_f} + U.\mathrm{bound}\bigl(\mathrm{esize}(S.\mathrm{prog}) + (\mathrm{esize}(n) + |q| + 1) + C_f(n)(|q|+1)^{k_f}\bigr) + (\mathrm{size}(s(n)) + 2)\bigl((s(n)+1)(4s(n)+14) + 7\,\mathrm{esize}(s(n)) + 8s(n) + 90\bigr) + 10 . $$
--
--   Theorem: if $C_f$ is polynomially bounded and $s = $ `S.dim` is polynomially bounded, then for every $k_f$ the function $n \mapsto Z(n)$ is polynomially bounded, that is, there is a polynomial $P$ with natural coefficients such that $Z(n) \le P(n)$ for all $n$.
--
--   $Z(n)$ is the quantity whose square bounds the cost of the *head* of the wrapper decider, the stage that queries the sampler's dimension through the universal machine and converts it to unary (`wrapHead_cost'` bounds that cost by $60\,Z(n)^2$ beyond the head's continuation), for a sampler running within $C_f(n)(|d|+1)^{k_f}$. Its polynomial boundedness is what `wrapCore_hasPolyCost` needs to bound the whole wrapper, which is what makes the verifier a string denotes $\lambda$-bounded.
--
--   **Formalization Note** `PolyBounded f := ∃ P : Polynomial ℕ, ∀ n, f n ≤ P.eval n`. `wrapHeadZ` is `noncomputable` and is exactly the displayed sum, with `esize x = (encode x : Data).size`, `(encode CL.Sampler.Query.dimension : Data).size` for $|q|$, `U.bound.eval` for the overhead polynomial and `Nat.size` for the bit length. The section variables `U : UniversalMachine` and `S : CL.Sampler ℓ` are explicit arguments and `ℓ` is implicit; `kf : ℕ` is explicit and enters only through the constant $(|q|+1)^{k_f}$; `Cf` is implicit with hypothesis `hCf : PolyBounded Cf`, and `hdim : PolyBounded S.dim`. Namespace `MIPRE.Cost.Prog`, module `MIPRE.Foundations.Halting.WrapperCost`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/WrapperCost.lean#L109-L128

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
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
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data
variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ)

theorem MIPRE.Cost.Prog.polyBounded_wrapHeadZ {Cf : ℕ → ℕ} (hCf : PolyBounded Cf) (kf : ℕ)
    (hdim : PolyBounded S.dim) : PolyBounded fun n => wrapHeadZ U S Cf kf n := by sorry
