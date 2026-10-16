-- Prove2me | Theorems.Thm_MIPRE_Verifier_exists_isBounded_lam
-- name    : MIPRE.Verifier.exists_isBounded_lam
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:27:10.8031+00:00
-- url     : https://prove2.me/theorems/6fcba47c-86c1-4a84-a757-53397e0c02a8
-- title:
--   A verifier with polynomially bounded programs and sampler dimension is $\lambda$-bounded for some $\lambda$
-- statement:
--   A normal form verifier $V$ with $\ell$ levels (`Verifier ℓ`) consists of a sampler — a closed program `sampler.prog` with a dimension function $s = $ `sampler.dim` $: \mathbb{N} \to \mathbb{N}$ and conditionally linear data — and a decider, a closed program, such that the decider accepts only questions of the sampler's dimension. `PolyBounded f` means $\exists P \in \mathbb{N}[X],\ \forall n,\ f(n) \le P(n)$. `Prog.HasPolyCost p` means that there are a polynomially bounded $C : \mathbb{N} \to \mathbb{N}$ and a degree $k$ such that for every index $n$ and every datum $d$, $p$ halts on `cons (encode n) d` within cost $C(n)\,(|d| + 1)^k$. `V.IsBounded λ` (blueprint `def:lambda-bounded`) says: for every $n \ge 2$, $s(n) \le n^\lambda$, the sampler halts on every input `cons (encode n) d` within cost $n^\lambda (|d| + 1)^\lambda$, and so does the decider (`TimeBoundAt n (n ^ λ) λ`); and the description length $|V| = \max(|\mathcal{S}|, |\mathcal{D}|)$ is at most $\lambda$. Assume `PolyBounded V.sampler.dim`, `V.sampler.prog.HasPolyCost` and `V.decider.prog.HasPolyCost`. Then
--
--   $$\exists\, \lambda \in \mathbb{N},\qquad V.\mathrm{IsBounded}\ \lambda .$$
--
--   `IsBounded` is the hypothesis every class membership of the halting reduction carries, and until this result nothing inhabited it unconditionally. Its threshold form `exists_isBounded` ($\exists n_0, \forall n \ge n_0, V.\mathrm{IsBounded}\ n$), which the classes consume, follows by monotonicity in $\lambda$; `Halting/WrapperCost.lean` discharges the `HasPolyCost` hypotheses for the verifier a string denotes.
--
--   **Formalization Note** The time clauses of `IsBounded` are guarded by $2 \le n$; `TimeBoundAt n T k` is `∀ d, HaltsWithin prog (cons (encode n) d) (T * (d.size + 1) ^ k)`, with `encode n` the binary encoding of $n$ and `d.size` the node count of the datum. The size clause `V.size ≤ lam` is part of `IsBounded` and is met by the $\lambda$ asserted. The verifier `V` is an explicit argument and `ℓ` implicit; the proposition is `MIPRE.Verifier.exists_isBounded_lam`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Bounded.lean#L116-L135

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

open MIPRE
open MIPRE.Verifier
open MIPRE.Cost
variable {ℓ : ℕ} (V : Verifier ℓ)

theorem MIPRE.Verifier.exists_isBounded_lam (hdim : PolyBounded V.sampler.dim)
    (hS : V.sampler.prog.HasPolyCost) (hD : V.decider.prog.HasPolyCost) :
    ∃ lam, V.IsBounded lam := by sorry
