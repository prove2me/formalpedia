-- Prove2me | Theorems.Thm_OrbNetEqui_Equivariance_corollary_S3
-- name    : OrbNetEqui.Equivariance.corollary_S3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:51.515018+00:00
-- url     : https://prove2.me/theorems/fd5ba8e7-c01e-4210-9026-0829f1325b3b
-- title:
--   Corollary S3, p. 24 — the diagonal reduction ψ(T)=Σ T(v⃗)Q^{v⃗} is injective, Σ_L n_L ≤ dim(V_u)^N, and ψ(g·T)_{ν,L} = U^L_g ψ(T)_{ν,L}
-- statement:
--   In the setting of Corollary S2 ($K$ a group, $(U^L)_L$ a complete catalogue of irreducible unitary representations, $V_u\simeq\bigoplus_a\mathbb V^{\mathrm{lab}(a)}$ with the block-diagonal action $\pi^2$, and $K$ acting on $V_u^{\otimes N}$ diagonally), there exist numbers $n_L\in\mathbb N$, nonzero for finitely many $L$, and tensor-independent coefficients $Q^{\vec v}_{\nu,L,M}$ such that the linear map
--   $$\big(\psi(\mathbf T_u)\big)_{\nu,L,M}:=\sum_{\vec v}T_u(v_1,\dots,v_N)\,Q^{\vec v}_{\nu,L,M},\qquad \nu\in\{1,\dots,n_L\}\qquad\text{(S31)}$$
--   satisfies:
--
--   1. $\psi$ is injective;
--   2. $\sum_L n_L\le\dim(V_u)^N$;
--   3. for every $k\in K$, $\psi(k\cdot\mathbf T_u)_{\nu,L}=U^L_k\,\psi(\mathbf T_u)_{\nu,L}$ (S32).
--
--   This is the equivariance of UNiTE's diagonal reduction layer, which the mission's goal theorem takes as a hypothesis on $\psi$.
--
--   **Formalization Note.** $\mathrm U(n)$ and $G_u$ are replaced by an arbitrary group $K$ with a complete catalogue, as in Theorem S1; equivariance is claimed for all of $K$. The corollary is stated, as in the paper, in the Definition S2 basis of $V_u$; the goal theorem works in a general basis $\{e_{u;v}\}$ with an arbitrary unitary representation $\pi^1_u$ and assumes (S32) for its $\psi_u$.
-- source:
--   Qiao et al., Informing Geometric Deep Learning with Electronic Interactions to Accelerate Quantum Chemistry, arXiv:2105.14655v4, p. 24, Corollary S3, eqs. (S31)–(S32)

import Mathlib
import Definitions.Def_OrbNetEqui_Equivariance_Basic

namespace OrbNetEqui.Equivariance

open Matrix

theorem corollary_S3 {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (hirr : ∀ L, IsIrreducibleUnitary (U L)) (hcat : CatalogComplete U)
    {r : ℕ} (lab : Fin r → Λ) (N : ℕ) :
    ∃ (μ : Λ → ℕ) (s : Finset Λ), (∀ L, L ∉ s → μ L = 0) ∧
      ∃ Q : (L : Λ) → Fin (μ L) → Fin (dim L) → (Fin N → Σ a : Fin r, Fin (dim (lab a))) → ℂ,
        Function.Injective (coeffMap Q) ∧
        ∑ L ∈ s, μ L ≤ Fintype.card (Σ a : Fin r, Fin (dim (lab a))) ^ N ∧
        ∀ (k : K) (T : (Fin N → Σ a : Fin r, Fin (dim (lab a))) → ℂ) (L : Λ) (ν : Fin (μ L)),
          coeffMap Q (diagAct (labelRep U lab k) T) L ν =
            (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ coeffMap Q T L ν := by sorry

end OrbNetEqui.Equivariance
