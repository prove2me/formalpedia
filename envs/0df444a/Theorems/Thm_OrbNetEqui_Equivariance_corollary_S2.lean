-- Prove2me | Theorems.Thm_OrbNetEqui_Equivariance_corollary_S2
-- name    : OrbNetEqui.Equivariance.corollary_S2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:45.771377+00:00
-- url     : https://prove2.me/theorems/ab9bb2d4-5c70-4e88-979b-56411d7b6440
-- title:
--   Corollary S2, p. 24 — an invertible equivariant linear map ψ : V_u^{⊗N} → ⊕_L (V^L)^{⊕μ(L;V_u)}
-- statement:
--   Let $K$ and the complete catalogue $(U^L)_{L\in\Lambda}$ of irreducible unitary representations be as in Theorem S1. Let $V_u\simeq\bigoplus_{a=1}^r\mathbb V^{\mathrm{lab}(a)}$ be a direct sum of catalogue spaces, listed with multiplicity by labels $\mathrm{lab}(1),\dots,\mathrm{lab}(r)$, on which $k$ acts block-diagonally by $\pi^2(k)=\bigoplus_a U^{\mathrm{lab}(a)}_k$ (Definition S2). Let $k$ act on $V_u^{\otimes N}$ diagonally by $\pi^2(k)^{\otimes N}$ (eq. (S27)).
--
--   Then there exist multiplicities $\mu(L;V_u)\in\mathbb N$, nonzero for finitely many $L$, and an invertible linear map
--   $$\psi:\ V_u^{\otimes N}\to V_u^\star:=\bigoplus_L(\mathbb V^L)^{\oplus\mu(L;V_u)}$$
--   such that for every tensor $\mathbf T_u$, every $k\in K$, every $L$ and every $\nu\le\mu(L;V_u)$,
--   $$\psi(k\cdot\mathbf T_u)_{\nu,L}=U^L_k\,\psi(\mathbf T_u)_{\nu,L}.$$
--
--   This produces the order-1 (vector) features from the diagonal blocks of an N-body tensor.
--
--   **Formalization Note.** The group $\mathrm U(n)$ (and its subgroup $G_u$) is replaced by an arbitrary group $K$ with a complete catalogue of irreducibles, and equivariance is claimed for every $k\in K$, which contains the paper's claim for $g_u\in G_u$. The basis of $V_u$ is the Definition S2 basis $\{\pi_{u;L,M}\}$.
-- source:
--   Qiao et al., Informing Geometric Deep Learning with Electronic Interactions to Accelerate Quantum Chemistry, arXiv:2105.14655v4, p. 24, Corollary S2

import Mathlib
import Definitions.Def_OrbNetEqui_Equivariance_Basic

namespace OrbNetEqui.Equivariance

open Matrix

theorem corollary_S2 {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (hirr : ∀ L, IsIrreducibleUnitary (U L)) (hcat : CatalogComplete U)
    {r : ℕ} (lab : Fin r → Λ) (N : ℕ) :
    ∃ (μ : Λ → ℕ) (s : Finset Λ), (∀ L, L ∉ s → μ L = 0) ∧
      ∃ ψ : ((Fin N → Σ a : Fin r, Fin (dim (lab a))) → ℂ) ≃ₗ[ℂ]
          ((L : Λ) → Fin (μ L) → Fin (dim L) → ℂ),
        ∀ (k : K) (T : (Fin N → Σ a : Fin r, Fin (dim (lab a))) → ℂ) (L : Λ) (ν : Fin (μ L)),
          ψ (diagAct (labelRep U lab k) T) L ν =
            (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ ψ T L ν := by sorry

end OrbNetEqui.Equivariance
