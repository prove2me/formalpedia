-- Prove2me | Theorems.Thm_GenSwitchHT_second_moment_finite
-- name    : GenSwitchHT.second_moment_finite
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:37.525208+00:00
-- url     : https://prove2.me/theorems/2e157320-3e6d-4c80-94a9-b67a269fc0c2
-- title:
--   Proof of Theorem 1, p.24 — finite steady-state second moment (corrected: $\nu$ has positive coordinates)
-- statement:
--   For a regime and every $\epsilon\in(0,1)$,
--
--   $$
--   \mathbb E\Bigl[\bigl\|\bar q^{(\epsilon)}\bigr\|^2\Bigr]<\infty .
--   $$
--
--   This is what licenses setting the drift of $\|q_{\parallel\mathcal H}\|^2$ to zero in steady state. No uniformity in $\epsilon$ is claimed.
--
--   Differences from the source:
--   - correction: any ν in the boundary of C → ν in the boundary of C with ν_i > 0 for every i (field ν_pos of Regime); reason: this item is a step of the proof of Theorem 1 and carries the setting of its corrected statement. The printed setting is false at a ν with a zero coordinate. Example satisfying every printed assumption: n = 2, one channel state, S = {(0,0),(1,0),(0,1)}, c = (1,1)/√2, b = 1/√2, ν = (0,1), a₁ = 0, a₂ = 2 with probability (1−ε)/2 and 0 otherwise. There p.6 asserts that λ^(ε) = (0, 1−ε) lies in the interior of C, which is false (it lies on the face x₁ = 0), and Theorem 1 fails: Σ_a = diag(0,1), H = ½·11ᵀ, Σ_B = 0, so (11) claims the limit ¼ for every w ∈ F, while q₁ = 0, q₂ is a single-server queue and ε E[⟨q̄,(0,1)⟩] → ½. Given ν ∈ C and b > 0, ν_i > 0 for every i is equivalent to the assertion of p.6
--   - generalization: L is the minimum number of half-spaces describing C → any finite description (c, b) of C by half-spaces with the normalization of p.6; reason: no step needs minimality once ν > 0; the minimal description is an instance
--   - generalization: ties in the arg max (4) are broken at random → the schedule has an arbitrary law on the arg max, depending on ε, q and m; reason: random tie-breaking is an instance
--   - generalization: q̄^(ε) is the limit in distribution of the chain, which is positive recurrent → stat ε is any PMF fixed by the one-step kernel, with no irreducibility assumed; reason: the limit in distribution of the paper is such a PMF; existence is not claimed (Solutions/verification/GenSwitchHT_Nonvacuous.lean exhibits an instance)
--   - reading: arrivals i.i.d. in time; their independence from the channel state and the schedule is not stated in Section 2 → given q, the channel state, the schedule and the arrivals are drawn in this order, the arrivals independently of the rest; reason: the order of events on p.5 gives it, and the proof uses it ("the channel state process is independent from the queue lengths process", p.6; "ā is independent of s̄", p.26)
--   - encoding: expectations of random variables → `expect` is the series ∑′ under a PMF on real queue vectors, arrivals valued in ℕⁿ, service vectors real and nonnegative; reason: the chain has countable reachable support; every series that is not automatically summable has a `HasExpect` clause here
-- source:
--   Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, proof of Theorem 1, p.24

import Mathlib
import Definitions.Def_GenSwitchHT_Model

open scoped BigOperators Matrix Topology

namespace GenSwitchHT

/-- Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, proof of Theorem 1, p.24:
the steady-state second moment `E[‖q̄‖²]` is finite, for every `ε ∈ (0, 1)`. No uniformity in `ε`
is claimed. -/
theorem second_moment_finite {n : ℕ} {M : Type*} [Fintype M] {L : ℕ} {G : Switch n M}
    {D : Description G L} (R : Regime D) {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    HasExpect (R.stat ε) (fun q => q ⬝ᵥ q) := by sorry

end GenSwitchHT
