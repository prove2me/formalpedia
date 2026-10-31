-- Prove2me | Theorems.Thm_GenSwitchHT_proposition_2
-- name    : GenSwitchHT.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:39.997342+00:00
-- url     : https://prove2.me/theorems/c820ebe0-a636-4b4a-87d9-58ea535a35d3
-- title:
--   Proposition 2 — state space collapse, uniform in $\epsilon$ (corrected: $\nu>0$; $T_t$ read as independent of $\epsilon$)
-- statement:
--   Let a regime with point $\nu$ be given, and let $P$ be the set of facets through $\nu$. Let $\delta>0$ be such that $\delta\le b^{(\ell)}-\langle c^{(\ell)},\nu\rangle$ for all $\ell\notin P$, and $\delta=1$ if every facet passes through $\nu$. For each $t=1,2,\dots$ there is a constant $T_t$ such that, for every $\epsilon\in(0,1)$ with $\epsilon<\delta/(2\|\nu\|)$,
--
--   $$
--   \mathbb E\Bigl[\bigl\|\bar q^{(\epsilon)}_{\perp\mathcal H}\bigr\|^t\Bigr]\le\mathbb E\Bigl[\bigl\|\bar q^{(\epsilon)}_{\perp\mathcal K}\bigr\|^t\Bigr]\le T_t ,
--   $$
--
--   where $\|q_{\perp\mathcal K}\|$ and $\|q_{\perp\mathcal H}\|$ are the Euclidean distances from $q$ to the cone $\mathcal K$ and to the subspace $\mathcal H$. Both expectations are finite.
--
--   As $\epsilon\downarrow0$ the queue vector grows like $1/\epsilon$, while its distance to $\mathcal K$ stays bounded in every moment: the state collapses to the cone. This drives the rest of the proof of Theorem 1.
--
--   Differences from the source:
--   - correction: any ν in the boundary of C → ν in the boundary of C with ν_i > 0 for every i (field ν_pos of Regime); reason: the uniform reading of the next entry is false when ν has a zero coordinate. Counterexample satisfying every printed assumption: n = 2, one channel state, S = {(0,0),(1,0),(0,1)}, c = (1,1)/√2, b = 1/√2, ν = (0,1) (so [L] \ P = ∅ and δ = 1), a₁ = 0, a₂ = 2 with probability (1−ε)/2 and 0 otherwise. Then q₁ = 0 in steady state, K is the ray spanned by (1,1), ‖q_⊥K‖ = q₂/√2, and q₂ is a single-server queue with ε E[q₂] → ½, so E[‖q_⊥K‖] is unbounded as ε ↓ 0. The positivity is equivalent to the assertion of p.6 that λ^(ε) lies in the interior of C, which fails at this ν, and Theorem 1 fails at this ν too
--   - reading: "If ε < δ/(2‖ν‖), then for each t there exists a constant T_t": whether T_t may depend on ε is not said → ∃ T_t, ∀ ε ∈ (0,1) with ε < δ/(2‖ν‖); reason: the stronger reading is taken, because the proof of Theorem 1 uses T_t as a constant in the O(·) of Claim 1 and (45); it implies the per-ε reading
--   - generalization: L is the minimum number of half-spaces describing C → any finite description (c, b) of C by half-spaces with the normalization of p.6; reason: no step needs minimality once ν > 0; the minimal description is an instance
--   - generalization: ties in the arg max (4) are broken at random → the schedule has an arbitrary law on the arg max, depending on ε, q and m; reason: random tie-breaking is an instance
--   - generalization: q̄^(ε) is the limit in distribution of the chain, which is positive recurrent → stat ε is any PMF fixed by the one-step kernel, with no irreducibility assumed; reason: the limit in distribution of the paper is such a PMF; existence is not claimed (Solutions/verification/GenSwitchHT_Nonvacuous.lean exhibits an instance)
--   - reading: arrivals i.i.d. in time; their independence from the channel state and the schedule is not stated in Section 2 → given q, the channel state, the schedule and the arrivals are drawn in this order, the arrivals independently of the rest; reason: the order of events on p.5 gives it, and the proof uses it ("the channel state process is independent from the queue lengths process", p.6; "ā is independent of s̄", p.26)
--   - encoding: expectations of random variables → `expect` is the series ∑′ under a PMF on real queue vectors, arrivals valued in ℕⁿ, service vectors real and nonnegative; reason: the chain has countable reachable support; every series that is not automatically summable has a `HasExpect` clause here
--   - encoding: ‖q_⊥K‖ and ‖q_⊥H‖ → Euclidean distances distTo to the sets K and H; reason: q − proj q has this norm, and no projection needs defining; both sets contain 0
-- source:
--   Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, Proposition 2, p.8

import Mathlib
import Definitions.Def_GenSwitchHT_Model

open scoped BigOperators Matrix Topology

namespace GenSwitchHT

/-- Proposition 2 of Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, p.8
(state space collapse), corrected: for `δ` as printed and each `t ≥ 1` there is a constant `T`,
**independent of `ε`**, with `E[‖q̄_⊥H‖ᵗ] ≤ E[‖q̄_⊥K‖ᵗ] ≤ T` for all `ε ∈ (0, 1)` with
`ε < δ/(2‖ν‖)`.

**Formalization Note.**
1. `‖q_⊥K‖` and `‖q_⊥H‖` are the Euclidean distances to `K` and `H`, so no projection is defined.
2. The printed text quantifies `ε` first. The proof of Theorem 1 uses `T` as a constant, so it is
stated uniformly. `ν > 0` is a field of `Regime`; without it the uniform form is false.
3. `δ = 1` when every facet passes through `ν`, as printed. -/
theorem proposition_2 {n : ℕ} {M : Type*} [Fintype M] {L : ℕ} {G : Switch n M}
    {D : Description G L} (R : Regime D) (δ : ℝ) (hδ : 0 < δ)
    (hδ_out : ∀ ℓ, ℓ ∉ D.activeSet R.ν → δ ≤ D.b ℓ - D.c ℓ ⬝ᵥ R.ν)
    (hδ_all : (∀ ℓ, ℓ ∈ D.activeSet R.ν) → δ = 1) (t : ℕ) (ht : 1 ≤ t) :
    ∃ T : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ε < δ / (2 * euclNorm R.ν) →
      HasExpect (R.stat ε) (fun q => distTo (D.hSub R.ν : Set (Fin n → ℝ)) q ^ t) ∧
      HasExpect (R.stat ε) (fun q => distTo (D.cone R.ν) q ^ t) ∧
      expect (R.stat ε) (fun q => distTo (D.hSub R.ν : Set (Fin n → ℝ)) q ^ t) ≤
        expect (R.stat ε) (fun q => distTo (D.cone R.ν) q ^ t) ∧
      expect (R.stat ε) (fun q => distTo (D.cone R.ν) q ^ t) ≤ T := by sorry

end GenSwitchHT
