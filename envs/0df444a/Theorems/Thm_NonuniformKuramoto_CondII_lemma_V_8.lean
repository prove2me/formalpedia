-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondII_lemma_V_8
-- name    : NonuniformKuramoto.CondII.lemma_V_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:56.383987+00:00
-- url     : https://prove2.me/theorems/4beff4d6-97b7-4144-8439-66cc0a67b693
-- title:
--   Lemma V.8 — the diagonal simplification (36): (Hθ)ᵀdiag(D_iD_j)HD⁻¹Hᵀdiag(P_ij cos φ_ij)sin(Hθ) = κ(Hθ)ᵀdiag(P_ij cos φ_ij)sin(Hθ)
-- statement:
--   Let $D_1,\dots,D_n>0$, $\kappa=\sum_{k=1}^nD_k$, let $P=P^T\in\mathbb R^{n\times n}$ and $\varphi\in\mathbb R^{n\times n}$, and let $\theta\in\Delta(\pi)$. With $H$ the incidence matrix of the complete graph and the pair-indexed diagonal matrices $\operatorname{diag}(D_iD_j)$ and $\operatorname{diag}(P_{ij}\cos\varphi_{ij})$,
--   $$
--   (H\theta)^T\operatorname{diag}(D_iD_j)\,HD^{-1}H^T\operatorname{diag}(P_{ij}\cos(\varphi_{ij}))\,\mathbf{sin}(H\theta)=\kappa\,(H\theta)^T\operatorname{diag}(P_{ij}\cos(\varphi_{ij}))\,\mathbf{sin}(H\theta).\tag{36}
--   $$
--
--   The left-hand side is the coupling term of the derivative (35) of the Lyapunov function $W$; the identity replaces the non-symmetric product $HD^{-1}H^T$ by the scalar $\kappa$, which is what makes $W$ a Lyapunov function for non-uniform $D_i$.
--
--   **Formalization Note** $D^{-1}=\operatorname{diag}(1/D_k)$, and the hypotheses $D_k>0$ are the model's. The weight on the pair $(i,j)$, $i<j$, is $P_{ij}\cos\varphi_{ij}$.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 24, Lemma V.8, (36)

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
open Matrix

namespace NonuniformKuramoto.CondII

/-- Lemma V.8 (Dörfler–Bullo, arXiv:0910.5673v4, p. 24), identity (36):
`(Hθ)ᵀ diag(D_iD_j) H D⁻¹ Hᵀ diag(P_ij cos ϕ_ij) sin(Hθ) = κ (Hθ)ᵀ diag(P_ij cos ϕ_ij) sin(Hθ)`,
with `H` the incidence matrix of the complete graph and `κ = ∑_k D_k`. -/
theorem lemma_V_8 {n : ℕ} (D : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) (θ : Fin n → ℝ)
    (hD : ∀ i, 0 < D i) (hP : ∀ i j, P i j = P j i) (hθ : NonuniformKuramoto.CondI.ArcOpen Real.pi θ) :
    (incH n *ᵥ θ) ⬝ᵥ (diagonal (pairDD D) *ᵥ (incH n *ᵥ (diagonal (fun k => (D k)⁻¹) *ᵥ
        ((incH n)ᵀ *ᵥ (diagonal (pairLossless P ϕ) *ᵥ sinv (incH n *ᵥ θ)))))) =
      kappa D * ((incH n *ᵥ θ) ⬝ᵥ (diagonal (pairLossless P ϕ) *ᵥ sinv (incH n *ᵥ θ))) := by sorry

end NonuniformKuramoto.CondII
