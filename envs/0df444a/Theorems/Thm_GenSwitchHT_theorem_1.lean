-- Prove2me | Theorems.Thm_GenSwitchHT_theorem_1
-- name    : GenSwitchHT.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:47.758474+00:00
-- url     : https://prove2.me/theorems/7ff264f3-f148-46b3-b9fc-8e0fcb963867
-- title:
--   Theorem 1 — steady-state mean of $\langle\bar q,w\rangle$ in heavy traffic (corrected: $\nu$ has positive coordinates)
-- statement:
--   Let a generalized switch operate under MaxWeight, with a heavy-traffic family indexed by $\epsilon\in(0,1)$: the mean arrival rate is $(1-\epsilon)\nu$, where $\nu$ is a point of the boundary of the capacity region $\mathcal C$ with $\nu_i>0$ for all $i$. Let $P$ be the set of facets through $\nu$, let $C$ be the matrix whose columns are a basis of $\{c^{(\ell)}:\ell\in P\}$, and let $H=C(C^TC)^{-1}C^T$ be the projection matrix onto their span. Let $\Sigma_a^{(\epsilon)}$ be the covariance matrix of the arrival vector and $\Sigma_B$ that of the channel-state variables $(b^{(\bar M,\ell)})_\ell$.
--
--   For every $w\in\bigcap_{\ell\in P}\mathcal F^{(\ell)}$, the expectation $\mathbb E[\langle\bar q^{(\epsilon)},w\rangle]$ is finite for each $\epsilon\in(0,1)$, and there is a function $K$ with $\epsilon K(\epsilon)\to0$ as $\epsilon\downarrow0$ such that for all $\epsilon\in(0,1)$
--
--   $$
--   \Bigl|\mathbb E\bigl[\langle\bar q^{(\epsilon)},w\rangle\bigr]-\frac1{2\epsilon}\mathbf 1^T\bigl(H\circ\Sigma_a^{(\epsilon)}\bigr)\mathbf 1-\frac1{2\epsilon}\mathbf 1^T\bigl((C^TC)^{-1}\circ\Sigma_B\bigr)\mathbf 1\Bigr|\le K(\epsilon).
--   $$
--
--   Further, if $\Sigma_a^{(\epsilon)}\to\Sigma_a$ component-wise as $\epsilon\downarrow0$, then
--
--   $$
--   \lim_{\epsilon\downarrow0}\epsilon\,\mathbb E\bigl[\langle\bar q^{(\epsilon)},w\rangle\bigr]=\frac12\Bigl(\mathbf 1^T(H\circ\Sigma_a)\mathbf 1+\mathbf 1^T\bigl((C^TC)^{-1}\circ\Sigma_B\bigr)\mathbf 1\Bigr).
--   $$
--
--   This is the main result of the paper. It computes the heavy-traffic scaling of the mean of a linear combination of the queue lengths when the complete resource pooling condition fails, that is, when $\nu$ may lie on several facets and the state collapses to a cone of dimension greater than one. The two terms on the right are the contributions of the randomness of the arrivals and of the channel.
--
--   Differences from the source:
--   - correction: any ν in the boundary of C → ν in the boundary of C with ν_i > 0 for every i (field ν_pos of Regime); reason: the printed statement is false when ν has a zero coordinate. Counterexample satisfying every printed assumption: n = 2, one channel state, S = {(0,0),(1,0),(0,1)}, c = (1,1)/√2, b = 1/√2, ν = (0,1), a₁ = 0, a₂ = 2 with probability (1−ε)/2 and 0 otherwise. Then Σ_a = diag(0,1), H = ½·11ᵀ, Σ_B = 0, so (11) claims the limit ¼ for every w ∈ F, while q₁ = 0, q₂ is a single-server queue and ε E[⟨q̄,(0,1)⟩] → ½. The positivity is equivalent to the claim of p.6 that λ^(ε) lies in the interior of C
--   - generalization: L is the minimum number of half-spaces describing C → any finite description (c, b) of C by half-spaces with the normalization of p.6; reason: no step needs minimality once ν > 0; the minimal description is an instance
--   - generalization: ties in the arg max (4) are broken at random → the schedule has an arbitrary law on the arg max, depending on ε, q and m; reason: random tie-breaking is an instance
--   - generalization: q̄^(ε) is the limit in distribution of the chain, which is positive recurrent → stat ε is any PMF fixed by the one-step kernel, with no irreducibility assumed; reason: the limit in distribution of the paper is such a PMF; existence is not claimed (Solutions/verification/GenSwitchHT_Nonvacuous.lean exhibits an instance)
--   - reading: arrivals i.i.d. in time; their independence from the channel state and the schedule is not stated in Section 2 → given q, the channel state, the schedule and the arrivals are drawn in this order, the arrivals independently of the rest; reason: the order of events on p.5 gives it, and the proof uses it ("the channel state process is independent from the queue lengths process", p.6; "ā is independent of s̄", p.26)
--   - encoding: expectations of random variables → `expect` is the series ∑′ under a PMF on real queue vectors, arrivals valued in ℕⁿ, service vectors real and nonnegative; reason: the chain has countable reachable support; every series that is not automatically summable has a `HasExpect` clause here
--   - encoding: Σ_B indexed by [L] × [L]; C and (CᵀC)⁻¹ indexed by P̃ → covBPt is the P̃ × P̃ block of Σ_B, and P̃ is any linearly independent subset of P spanning H; reason: the Hadamard product with (CᵀC)⁻¹ only types on P̃; the column-space sentence of p.7 is the field Pt_span
-- source:
--   Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, Theorem 1, eqs. (10)–(11), p.9

import Mathlib
import Definitions.Def_GenSwitchHT_Model

open scoped BigOperators Matrix Topology

namespace GenSwitchHT

/-- Theorem 1 of Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, p.9, corrected
to `ν > 0` (the field `ν_pos` of `Regime`). For every `w ∈ ∩_{ℓ∈P} F^(ℓ)`:
1. `E[⟨q̄^(ε), w⟩]` is finite for every `ε ∈ (0, 1)`;
2. eq. (10): there is `K` with `εK(ε) → 0` as `ε ↓ 0` and
`|E[⟨q̄^(ε), w⟩] - (1/2ε) 1ᵀ(H ∘ Σ_a^(ε))1 - (1/2ε) 1ᵀ((CᵀC)⁻¹ ∘ Σ_B)1| ≤ K(ε)` on `(0, 1)`;
3. eq. (11): if `Σ_a^(ε) → Sa` component-wise as `ε ↓ 0`, then
`ε E[⟨q̄^(ε), w⟩] → (1/2)(1ᵀ(H ∘ Sa)1 + 1ᵀ((CᵀC)⁻¹ ∘ Σ_B)1)`.

**Formalization Note.** `P̃` is any basis of the family `{c^(ℓ) : ℓ ∈ P}`, the `ActiveBasis`. The
family `(α, τ, stat)` is any member of `Regime`. -/
theorem theorem_1 {n : ℕ} {M : Type*} [Fintype M] {L : ℕ} {G : Switch n M}
    {D : Description G L} (R : Regime D) (B : ActiveBasis D R.ν) (w : Fin n → ℝ)
    (hw : ∀ ℓ ∈ D.activeSet R.ν, w ∈ D.facet ℓ) :
    (∀ ε : ℝ, 0 < ε → ε < 1 → HasExpect (R.stat ε) fun q => q ⬝ᵥ w) ∧
    (∃ K : ℝ → ℝ, Filter.Tendsto (fun ε => ε * K ε) (𝓝[>] 0) (𝓝 0) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        |R.meanQ w ε - 1 / (2 * ε) * B.arrivalTerm (covArrival (R.α ε)) -
          1 / (2 * ε) * B.serviceTerm| ≤ K ε) ∧
    ∀ Sa : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, Filter.Tendsto (fun ε => covArrival (R.α ε) i j) (𝓝[>] 0) (𝓝 (Sa i j))) →
      Filter.Tendsto (fun ε => ε * R.meanQ w ε) (𝓝[>] 0)
        (𝓝 ((1 / 2) * (B.arrivalTerm Sa + B.serviceTerm))) := by sorry

end GenSwitchHT
