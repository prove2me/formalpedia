-- Prove2me | Theorems.Thm_GenSwitchHT_eq_44
-- name    : GenSwitchHT.eq_44
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:56.362751+00:00
-- url     : https://prove2.me/theorems/53b68e64-a03c-4572-b637-f3f25ea10278
-- title:
--   Eq. (44) — $\mathcal T_3=O(\epsilon)$ (corrected: $\nu$ has positive coordinates)
-- statement:
--   For a regime with basis $\tilde P$, there are constants $C,\epsilon_0>0$ such that for $\epsilon\in(0,\epsilon_0)$
--
--   $$
--   0\le\mathcal T_3\le C\epsilon ,
--   $$
--
--   where $\mathcal T_3=\mathbb E[\|\bar u_{\parallel\mathcal H}\|^2]$. The term coming from the unused service is thus negligible in the drift identity.
--
--   Differences from the source:
--   - correction: any ν in the boundary of C → ν in the boundary of C with ν_i > 0 for every i (field ν_pos of Regime); reason: this item is a step of the proof of Theorem 1 and carries the setting of its corrected statement. The printed setting is false at a ν with a zero coordinate. Example satisfying every printed assumption: n = 2, one channel state, S = {(0,0),(1,0),(0,1)}, c = (1,1)/√2, b = 1/√2, ν = (0,1), a₁ = 0, a₂ = 2 with probability (1−ε)/2 and 0 otherwise. There p.6 asserts that λ^(ε) = (0, 1−ε) lies in the interior of C, which is false (it lies on the face x₁ = 0), and Theorem 1 fails: Σ_a = diag(0,1), H = ½·11ᵀ, Σ_B = 0, so (11) claims the limit ¼ for every w ∈ F, while q₁ = 0, q₂ is a single-server queue and ε E[⟨q̄,(0,1)⟩] → ½. Given ν ∈ C and b > 0, ν_i > 0 for every i is equivalent to the assertion of p.6
--   - generalization: L is the minimum number of half-spaces describing C → any finite description (c, b) of C by half-spaces with the normalization of p.6; reason: no step needs minimality once ν > 0; the minimal description is an instance
--   - generalization: ties in the arg max (4) are broken at random → the schedule has an arbitrary law on the arg max, depending on ε, q and m; reason: random tie-breaking is an instance
--   - generalization: q̄^(ε) is the limit in distribution of the chain, which is positive recurrent → stat ε is any PMF fixed by the one-step kernel, with no irreducibility assumed; reason: the limit in distribution of the paper is such a PMF; existence is not claimed (Solutions/verification/GenSwitchHT_Nonvacuous.lean exhibits an instance)
--   - reading: arrivals i.i.d. in time; their independence from the channel state and the schedule is not stated in Section 2 → given q, the channel state, the schedule and the arrivals are drawn in this order, the arrivals independently of the rest; reason: the order of events on p.5 gives it, and the proof uses it ("the channel state process is independent from the queue lengths process", p.6; "ā is independent of s̄", p.26)
--   - encoding: expectations of random variables → `expect` is the series ∑′ under a PMF on real queue vectors, arrivals valued in ℕⁿ, service vectors real and nonnegative; reason: the chain has countable reachable support; every series that is not automatically summable has a `HasExpect` clause here
--   - encoding: Σ_B indexed by [L] × [L]; C and (CᵀC)⁻¹ indexed by P̃ → covBPt is the P̃ × P̃ block of Σ_B, and P̃ is any linearly independent subset of P spanning H; reason: the Hadamard product with (CᵀC)⁻¹ only types on P̃; the column-space sentence of p.7 is the field Pt_span
--   - encoding: O(·) as ε ↓ 0 → there are C, ε₀ > 0 not depending on ε with the bound on (0, ε₀) ∩ (0, 1); reason: the meaning of the notation, for the fixed family
-- source:
--   Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, proof of Theorem 1, eq. (44), p.26

import Mathlib
import Definitions.Def_GenSwitchHT_Model

open scoped BigOperators Matrix Topology

namespace GenSwitchHT

/-- Eq. (44) of Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, proof of Theorem
1, p.26: `T₃ = O(ε)`, with `0 ≤ T₃` as in the display above it on the same page. -/
theorem eq_44 {n : ℕ} {M : Type*} [Fintype M] {L : ℕ} {G : Switch n M}
    {D : Description G L} (R : Regime D) (B : ActiveBasis D R.ν) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε < 1 →
      0 ≤ R.T3 B ε ∧ R.T3 B ε ≤ C * ε := by sorry

end GenSwitchHT
