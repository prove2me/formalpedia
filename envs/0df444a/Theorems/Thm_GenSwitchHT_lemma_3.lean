-- Prove2me | Theorems.Thm_GenSwitchHT_lemma_3
-- name    : GenSwitchHT.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:39.402457+00:00
-- url     : https://prove2.me/theorems/a8adf4d5-9ddc-41db-a352-425544052881
-- title:
--   Lemma 3 — the schedule lies on the active faces with probability $1-O(\epsilon)$ (corrected: $\nu$ has positive coordinates)
-- statement:
--   For a regime, a channel state $m$ with $\psi_m\ne0$ and $\ell\in P$, let
--
--   $$
--   \pi^{(m,\ell)}=\mathbb P\bigl[\langle c^{(\ell)},\bar s\rangle=b^{(m,\ell)}\bigm|\bar M=m\bigr].
--   $$
--
--   There is a constant $C$, not depending on $\epsilon$, such that $1-\pi^{(m,\ell)}\le C\epsilon$ for every $\epsilon\in(0,1)$.
--
--   In heavy traffic, MaxWeight in channel state $m$ picks a schedule on the active faces of $\mathrm{ConvexHull}(\mathcal S^{(m)})$ with high probability. This turns the moments of $\bar s$ into the covariance $\Sigma_B$.
--
--   Differences from the source:
--   - correction: any ν in the boundary of C → ν in the boundary of C with ν_i > 0 for every i (field ν_pos of Regime); reason: this item is a step of the proof of Theorem 1 and carries the setting of its corrected statement. The printed setting is false at a ν with a zero coordinate. Example satisfying every printed assumption: n = 2, one channel state, S = {(0,0),(1,0),(0,1)}, c = (1,1)/√2, b = 1/√2, ν = (0,1), a₁ = 0, a₂ = 2 with probability (1−ε)/2 and 0 otherwise. There p.6 asserts that λ^(ε) = (0, 1−ε) lies in the interior of C, which is false (it lies on the face x₁ = 0), and Theorem 1 fails: Σ_a = diag(0,1), H = ½·11ᵀ, Σ_B = 0, so (11) claims the limit ¼ for every w ∈ F, while q₁ = 0, q₂ is a single-server queue and ε E[⟨q̄,(0,1)⟩] → ½. Given ν ∈ C and b > 0, ν_i > 0 for every i is equivalent to the assertion of p.6
--   - generalization: L is the minimum number of half-spaces describing C → any finite description (c, b) of C by half-spaces with the normalization of p.6; reason: no step needs minimality once ν > 0; the minimal description is an instance
--   - generalization: ties in the arg max (4) are broken at random → the schedule has an arbitrary law on the arg max, depending on ε, q and m; reason: random tie-breaking is an instance
--   - generalization: q̄^(ε) is the limit in distribution of the chain, which is positive recurrent → stat ε is any PMF fixed by the one-step kernel, with no irreducibility assumed; reason: the limit in distribution of the paper is such a PMF; existence is not claimed (Solutions/verification/GenSwitchHT_Nonvacuous.lean exhibits an instance)
--   - reading: arrivals i.i.d. in time; their independence from the channel state and the schedule is not stated in Section 2 → given q, the channel state, the schedule and the arrivals are drawn in this order, the arrivals independently of the rest; reason: the order of events on p.5 gives it, and the proof uses it ("the channel state process is independent from the queue lengths process", p.6; "ā is independent of s̄", p.26)
--   - encoding: expectations of random variables → `expect` is the series ∑′ under a PMF on real queue vectors, arrivals valued in ℕⁿ, service vectors real and nonnegative; reason: the chain has countable reachable support; every series that is not automatically summable has a `HasExpect` clause here
--   - encoding: π^(m,ℓ) for each m ∈ M → hitProb is the ratio of the two probabilities, stated for ψ_m ≠ 0; reason: the conditional probability is undefined otherwise
-- source:
--   Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, Lemma 3, p.24

import Mathlib
import Definitions.Def_GenSwitchHT_Model

open scoped BigOperators Matrix Topology

namespace GenSwitchHT

/-- Lemma 3 of Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, p.24: for each
`m` with `ψ_m ≠ 0` and each `ℓ ∈ P`, `1 - π^(m,ℓ)` is `O(ε)`.

**Formalization Note.** The conditional probability given `M̄ = m` is only defined for `ψ_m ≠ 0`.
The constant `C` may depend on `m` and `ℓ`, not on `ε`. -/
theorem lemma_3 {n : ℕ} {M : Type*} [Fintype M] {L : ℕ} {G : Switch n M}
    {D : Description G L} (R : Regime D) (m : M) (hm : G.ψ m ≠ 0) (ℓ : Fin L)
    (hℓ : ℓ ∈ D.activeSet R.ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → 1 - R.hitProb ε m ℓ ≤ C * ε := by sorry

end GenSwitchHT
