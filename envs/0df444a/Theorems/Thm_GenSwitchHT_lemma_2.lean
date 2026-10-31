-- Prove2me | Theorems.Thm_GenSwitchHT_lemma_2
-- name    : GenSwitchHT.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:42.175419+00:00
-- url     : https://prove2.me/theorems/b2d7268f-9038-4e4c-bf27-e5eea985741c
-- title:
--   Lemma 2 — the service maxima and the common decomposition of $\nu$
-- statement:
--   Let $\nu$ be a point of the boundary of $\mathcal C$, and $P$ the set of facets through it. Then:
--
--   1. for every $\ell$ and $m$ there is $x\in\mathcal S^{(m)}$ with $b^{(m,\ell)}=\langle c^{(\ell)},x\rangle$;
--   2. for every $\ell\in P$,
--   $$
--   b^{(\ell)}=\mathbb E\bigl[\bar B_\ell\bigr]=\sum_{m\in\mathcal M}\psi_m\,b^{(m,\ell)} ;
--   $$
--   3. there are $\nu^{(m)}\in\mathrm{ConvexHull}(\mathcal S^{(m)})$ with $\nu=\sum_m\psi_m\nu^{(m)}$ and $\langle c^{(\ell)},\nu^{(m)}\rangle=b^{(m,\ell)}$ for all $\ell\in P$ and all $m$ with $\psi_m\ne0$.
--
--   So a point of a face of $\mathcal C$ splits over the channel states into points of the matching faces of the convex hulls. This links the channel-state variables $\bar B_\ell$ to the facets.
--
--   Differences from the source:
--   - generalization: ν^(m) ∈ S^(m) for ℓ ∈ P, and b^(ℓ) = E[B̄_ℓ] → the same for all ℓ in clause 1, and a third clause: one decomposition ν = Σ ψ_m ν^(m) with ν^(m) in the convex hull, tight for all ℓ ∈ P at once; reason: Appendix D.1 and Claim 1 use this decomposition. It has the convex hull because the step ν^(m) ∈ S^(m) of D.1 is false (one channel state, S = {(0,0),(1,0),(0,1)}, ν = (½,½) ∉ S); the printed lemma is clause 1 and 2, where the vector may depend on ℓ
--   - generalization: L is the minimum number of half-spaces describing C → any finite description (c, b) of C by half-spaces with the normalization of p.6; reason: no step needs minimality once ν > 0; the minimal description is an instance
-- source:
--   Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, Lemma 2, p.24, with its proof in Appendix D.1, pp.40–41

import Mathlib
import Definitions.Def_GenSwitchHT_Model

open scoped BigOperators Matrix Topology

namespace GenSwitchHT

/-- Lemma 2 of Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, p.24, with
the common decomposition of its proof in Appendix D.1, pp.40–41: (a) `b^(m,ℓ)` is attained on
`S^(m)`; (b) `b^(ℓ) = E[B̄_ℓ]` for `ℓ ∈ P`; (c) `ν = ∑ ψ_m ν^(m)` with `ν^(m)` in the convex hull of
`S^(m)` and `⟨c^(ℓ), ν^(m)⟩ = b^(m,ℓ)` for all `ℓ ∈ P` at once.

**Formalization Note.** The vector `ν^(m)` of (a) depends on `ℓ`. Clause (c) is what Appendix D.1
and Claim 1 use. It has the convex hull, because `ν^(m) ∈ S^(m)` of Appendix D.1 is false. -/
theorem lemma_2 {n : ℕ} {M : Type*} [Fintype M] {L : ℕ} {G : Switch n M}
    (D : Description G L) (ν : Fin n → ℝ) (hν : ν ∈ frontier G.capacityRegion) :
    (∀ (ℓ : Fin L) (m : M), ∃ x ∈ G.S m, D.bm m ℓ = D.c ℓ ⬝ᵥ x) ∧
    (∀ ℓ ∈ D.activeSet ν, D.b ℓ = expect G.ψ fun m => D.bm m ℓ) ∧
    ∃ y : M → (Fin n → ℝ), (∀ m, y m ∈ convexHull ℝ (G.S m : Set (Fin n → ℝ))) ∧
      ν = ∑ m, (G.ψ m).toReal • y m ∧
      ∀ ℓ ∈ D.activeSet ν, ∀ m, G.ψ m ≠ 0 → D.c ℓ ⬝ᵥ y m = D.bm m ℓ := by sorry

end GenSwitchHT
