-- Prove2me | Theorems.Thm_LocalSweepFT_claim_5_9
-- name    : LocalSweepFT.claim_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:42:29.681247+00:00
-- url     : https://prove2.me/theorems/4706833f-f9b1-4b27-973d-26caec124675
-- title:
--   Claim 5.9 — barrier argument: a logical change forces a syndrome component of size $>cn$
-- statement:
--   Let $d'\ge2$ and $d-d'\ge2$. There is a constant $c\in(0,1)$, depending only on $d,d'$, and a threshold $n_0$ such that for every $n\ge n_0$: if $x_1,\dots,x_t$ are $d'$-chains of the side-$n$ torus $\mathcal T^d_n$ with $x_1$ trivial, consecutive chains at Hamming distance at most one, and every connected component of every $\partial^-x_i$ of size at most $cn$, then
--   $$[0]=[x_1]=[x_2]=\dots=[x_t].$$
--
--   Equivalently, a sequence of single-qubit changes that ends in a non-trivial logical class passes through a syndrome with a connected component of linear size; this is the barrier the contour analysis rules out.
--
--   Differences from the source:
--   - encoding: standing assumption "Fix integers d, d′ satisfying d′, d − d′ ≥ 2" (p.4) → hypotheses 2 ≤ d′ and 2 ≤ d − d′; reason: the section's standing assumption is a hypothesis of each statement
--   - generalization: x₁ is a trivial chain → x₁ ∈ im ∂⁻ (an X-stabilizer); reason: x₁ = 0 is a special case; the filling class of a stabilizer is [0]
--   - generalization: the Hamming distance between x_i and x_{i+1} is one → at most one; reason: sequences with distance exactly one are a special case; the proof uses "at most one" (p.43)
--   - reading: [x_i] defined from one canonical filling per component (Def 5.7) → [x_i] = [0] for every small filling, together with the existence of one; reason: at least as strong as the canonical choice
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 5.9, p.42

import Mathlib
import Definitions.Def_LocalSweepFT_BarrierProp

namespace LocalSweepFT

/-- Claim 5.9, p.42 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). There is a constant `c ∈ (0, 1)`, depending only on
`d, d′`, such that for all sufficiently large `n`: if `x₁, …, x_t ∈ C_{d′}(T^d_n)` with `x₁` trivial,
consecutive chains at Hamming distance one, and every connected component of every `∂⁻x_i` of size
at most `cn`, then `[0] = [x₁] = [x₂] = … = [x_t]` (`BarrierProp d d′ n 1 c`).

**Formalization Note.** "`x₁` is a trivial chain" is read as `x₁ ∈ im ∂⁻` (an X-stabilizer), which
contains `x₁ = 0`. Consecutive chains are at distance `≤ 1` (repetitions allowed). `[x_i] = [0]` is
required for every choice of small fillings, together with the existence of one. Standing
assumption `d′, d − d′ ≥ 2` (p.4). -/
theorem claim_5_9 (d d' : ℕ) (h1 : 2 ≤ d') (h2 : 2 ≤ d - d') :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → BarrierProp d d' n 1 c := by sorry

end LocalSweepFT
