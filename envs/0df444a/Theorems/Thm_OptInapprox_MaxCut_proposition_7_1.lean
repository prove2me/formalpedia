-- Prove2me | Theorems.Thm_OptInapprox_MaxCut_proposition_7_1
-- name    : OptInapprox.MaxCut.proposition_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:07.440305+00:00
-- url     : https://prove2.me/theorems/1e5ae896-2e06-40e2-95d1-af728a0a8341
-- title:
--   Proposition 7.1, p. 16 — 𝕊_ρ(f) = ⟨f, T_ρ f⟩ = Σ_S ρ^{|S|} f̂(S)²
-- statement:
--   Let $f:\{-1,1\}^n\to\mathbb R$ and $\rho\in[-1,1]$. Then
--   $$\mathbb S_\rho(f)=\langle f,T_\rho f\rangle=\sum_{S\subseteq[n]}\rho^{|S|}\hat f(S)^2,$$
--   where $\mathbb S_\rho$ is the noise stability, $T_\rho$ the Bonami–Beckner operator, $\langle f,g\rangle=\mathbf E[fg]$ and $\hat f(S)$ the Fourier coefficients.
--
--   This is the Fourier formula for noise stability, used to compare noise stabilities of a function and its smoothing.
--
--   **Formalization Note.** $\rho^{0}=1$, also at $\rho=0$.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 16, Proposition 7.1

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Cube

namespace OptInapprox.MaxCut

theorem proposition_7_1 {n : ℕ} (f : (Fin n → Bool) → ℝ) (ρ : ℝ) (hρ₁ : -1 ≤ ρ) (hρ₂ : ρ ≤ 1) :
    noiseStab ρ f = cubeE (fun x => f x * bonamiBeckner ρ f x) ∧
      noiseStab ρ f = ∑ S : Finset (Fin n), ρ ^ S.card * fourier f S ^ 2 := by sorry

end OptInapprox.MaxCut
