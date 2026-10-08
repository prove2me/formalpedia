-- Prove2me | Theorems.Thm_MinRankRecovery_RandomRIP_lemma_4_4
-- name    : MinRankRecovery.RandomRIP.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:28.616179+00:00
-- url     : https://prove2.me/theorems/21f71ee2-9b6c-4816-8a44-fad8927e05d4
-- title:
--   Lemma 4.4 — near isometry is stable under perturbing the subspace: δ′ = δ + (1 + ‖A‖)ρ(U₁, U₂)
-- statement:
--   Let $\mathcal A:\mathbb R^D\to\mathbb R^p$ be a linear map with operator norm $\|\mathcal A\|$, and let $U_1,U_2\subseteq\mathbb R^D$ be subspaces of the same dimension $d$. Suppose that for some $0<\delta<1$,
--   $$(1-\delta)\|X\|\le\|\mathcal A(X)\|\le(1+\delta)\|X\|\qquad\text{for all }X\in U_1.$$
--   Then for all $Y\in U_2$,
--   $$(1-\delta')\|Y\|\le\|\mathcal A(Y)\|\le(1+\delta')\|Y\|,\qquad \delta'=\delta+(1+\|\mathcal A\|)\,\rho(U_1,U_2),$$
--   where $\rho(U_1,U_2)=\|P_{U_1}-P_{U_2}\|$ is the projection distance.
--
--   The lemma is deterministic. It quantifies how the isometry constant changes as one moves through the Grassmannian, which is what allows a finite net of subspaces to control all of them.
--
--   **Formalization Note** $\mathbb R^D$ is `EuclideanSpace ℝ ι` for an arbitrary finite index type $\iota$ ($D=|\iota|$); taking $\iota=\{1,\dots,m\}\times\{1,\dots,n\}$ gives the space of vectorized $m\times n$ matrices with the Frobenius norm. $\mathcal A$ is a continuous linear map into `EuclideanSpace ℝ (Fin p)` and $\|\mathcal A\|$ its operator norm. No bound $\delta'<1$ is assumed.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, Lemma 4.4, (4.11)–(4.13), p. 17

import Mathlib
import Definitions.Def_MinRankRecovery_RandomRIP_SubspaceDist

namespace MinRankRecovery.RandomRIP

/-- Lemma 4.4, p. 17: if a linear map `A : ℝ^D → ℝᵖ` is a `δ`-isometry on a `d`-dimensional
subspace `U₁` (0 < δ < 1), then it is a `δ′`-isometry on every `d`-dimensional subspace `U₂`,
with `δ′ = δ + (1 + ‖A‖) ρ(U₁, U₂)`. Here `ℝ^D` is `EuclideanSpace ℝ ι` for a finite index
type `ι` (`D = card ι`), `‖·‖` is its Euclidean norm (the paper's `‖·‖_F`) and `‖A‖` the
operator norm. -/
theorem lemma_4_4 {ι : Type} [Fintype ι] {p d : ℕ}
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin p))
    (U₁ U₂ : Submodule ℝ (EuclideanSpace ℝ ι))
    (hU₁ : Module.finrank ℝ U₁ = d) (hU₂ : Module.finrank ℝ U₂ = d)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hiso : ∀ X ∈ U₁, (1 - δ) * ‖X‖ ≤ ‖A X‖ ∧ ‖A X‖ ≤ (1 + δ) * ‖X‖) :
    ∀ Y ∈ U₂,
      (1 - (δ + (1 + ‖A‖) * projDist U₁ U₂)) * ‖Y‖ ≤ ‖A Y‖ ∧
        ‖A Y‖ ≤ (1 + (δ + (1 + ‖A‖) * projDist U₁ U₂)) * ‖Y‖ := by sorry

end MinRankRecovery.RandomRIP
