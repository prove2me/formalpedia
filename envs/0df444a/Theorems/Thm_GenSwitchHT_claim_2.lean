-- Prove2me | Theorems.Thm_GenSwitchHT_claim_2
-- name    : GenSwitchHT.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:36.70334+00:00
-- url     : https://prove2.me/theorems/e2c77fc1-382a-420b-895e-d6708db902fd
-- title:
--   Claim 2 — the unused service on the active facets (corrected: $\nu$ has positive coordinates)
-- statement:
--   For a regime, there are constants $C,\epsilon_0>0$ such that for $\epsilon\in(0,\epsilon_0)$
--
--   $$
--   0\le\epsilon\sum_{\ell\in P}b^{(\ell)}-\sum_{\ell\in P}\mathbb E\bigl[\langle c^{(\ell)},\bar u\rangle\bigr]\le C\epsilon ,
--   $$
--
--   that is, $\sum_{\ell\in P}\mathbb E[\langle c^{(\ell)},\bar u\rangle]=\epsilon\sum_{\ell\in P}b^{(\ell)}-O(\epsilon)$. This bounds the terms of the drift identity that involve the unused service.
--
--   Differences from the source:
--   - correction: any ν in the boundary of C → ν in the boundary of C with ν_i > 0 for every i (field ν_pos of Regime); reason: this item is a step of the proof of Theorem 1 and carries the setting of its corrected statement. The printed setting is false at a ν with a zero coordinate. Example satisfying every printed assumption: n = 2, one channel state, S = {(0,0),(1,0),(0,1)}, c = (1,1)/√2, b = 1/√2, ν = (0,1), a₁ = 0, a₂ = 2 with probability (1−ε)/2 and 0 otherwise. There p.6 asserts that λ^(ε) = (0, 1−ε) lies in the interior of C, which is false (it lies on the face x₁ = 0), and Theorem 1 fails: Σ_a = diag(0,1), H = ½·11ᵀ, Σ_B = 0, so (11) claims the limit ¼ for every w ∈ F, while q₁ = 0, q₂ is a single-server queue and ε E[⟨q̄,(0,1)⟩] → ½. Given ν ∈ C and b > 0, ν_i > 0 for every i is equivalent to the assertion of p.6
--   - generalization: L is the minimum number of half-spaces describing C → any finite description (c, b) of C by half-spaces with the normalization of p.6; reason: no step needs minimality once ν > 0; the minimal description is an instance
--   - generalization: ties in the arg max (4) are broken at random → the schedule has an arbitrary law on the arg max, depending on ε, q and m; reason: random tie-breaking is an instance
--   - generalization: q̄^(ε) is the limit in distribution of the chain, which is positive recurrent → stat ε is any PMF fixed by the one-step kernel, with no irreducibility assumed; reason: the limit in distribution of the paper is such a PMF; existence is not claimed (Solutions/verification/GenSwitchHT_Nonvacuous.lean exhibits an instance)
--   - reading: arrivals i.i.d. in time; their independence from the channel state and the schedule is not stated in Section 2 → given q, the channel state, the schedule and the arrivals are drawn in this order, the arrivals independently of the rest; reason: the order of events on p.5 gives it, and the proof uses it ("the channel state process is independent from the queue lengths process", p.6; "ā is independent of s̄", p.26)
--   - encoding: expectations of random variables → `expect` is the series ∑′ under a PMF on real queue vectors, arrivals valued in ℕⁿ, service vectors real and nonnegative; reason: the chain has countable reachable support; every series that is not automatically summable has a `HasExpect` clause here
--   - encoding: the term − O(ε) of (43) → both bounds on it: it is subtracted, nonnegative and at most Cε, for C, ε₀ > 0 not depending on ε; reason: the sign is that of the print; the nonnegativity comes from E⟨c^(ℓ), s̄⟩ ≤ b^(ℓ)
-- source:
--   Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, Claim 2, eq. (43), p.26

import Mathlib
import Definitions.Def_GenSwitchHT_Model

open scoped BigOperators Matrix Topology

namespace GenSwitchHT

/-- Claim 2 of Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, eq. (43), p.26:
`∑_{ℓ∈P} E[⟨c^(ℓ), ū⟩] = ε ∑_{ℓ∈P} b^(ℓ) - O(ε)`.

**Formalization Note.** The term `O(ε)` is subtracted, and it is nonnegative: both are stated. -/
theorem claim_2 {n : ℕ} {M : Type*} [Fintype M] {L : ℕ} {G : Switch n M}
    {D : Description G L} (R : Regime D) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε < 1 →
      0 ≤ ε * ∑ ℓ ∈ D.activeSet R.ν, D.b ℓ -
        ∑ ℓ ∈ D.activeSet R.ν, expect (R.steady ε) (fun ω => D.c ℓ ⬝ᵥ ω.u) ∧
      ε * ∑ ℓ ∈ D.activeSet R.ν, D.b ℓ -
        ∑ ℓ ∈ D.activeSet R.ν, expect (R.steady ε) (fun ω => D.c ℓ ⬝ᵥ ω.u) ≤ C * ε := by sorry

end GenSwitchHT
