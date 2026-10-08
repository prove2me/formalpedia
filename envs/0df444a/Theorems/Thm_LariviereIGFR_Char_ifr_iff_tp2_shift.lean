-- Prove2me | Theorems.Thm_LariviereIGFR_Char_ifr_iff_tp2_shift
-- name    : LariviereIGFR.Char.ifr_iff_tp2_shift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:11.665022+00:00
-- url     : https://prove2.me/theorems/84fe4e49-23ef-4f7e-b96d-e96e4f96b36c
-- title:
--   Proof of Theorem 1, p. 603 (Barlow–Proschan 1965) — IFR iff Φ̄(ξ − θ) is TP₂
-- statement:
--   Let $\nu$ be a probability law on $\mathbb R$ (not necessarily nonnegative) with distribution function $\Phi$ and regular density $\psi$. Then $\nu$ is IFR if and only if
--   $$f(\xi, \theta) = \bar\Phi(\xi - \theta)$$
--   is TP₂ on $\mathbb R \times \mathbb R$, that is, $\bar\Phi(\xi_1 - \theta_1)\bar\Phi(\xi_2 - \theta_2) - \bar\Phi(\xi_1 - \theta_2)\bar\Phi(\xi_2 - \theta_1) \ge 0$ whenever $\xi_1 < \xi_2$ and $\theta_1 < \theta_2$.
--
--   This classical characterization (Barlow and Proschan 1965) is cited in the proof of Theorem 1 and applied to $X_L = \log X$, which can take negative values; it is therefore stated for an arbitrary law on $\mathbb R$.
--
--   **Formalization Note** IFR is weak monotonicity of $h = \psi/\bar\Phi$ on $\{\Phi < 1\}$, with $\psi$ the regular version of the density (the derivative of $\Phi$ on the support, $0$ to its left).
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §2, proof of Theorem 1, citing Barlow and Proschan (1965) ("X_L is IFR if and only if f_L(ξ, θ) = Φ̄_L(ξ − θ) is TP₂")

import Mathlib
import Definitions.Def_LariviereIGFR_Char_Setting

namespace LariviereIGFR.Char

open MeasureTheory ProbabilityTheory

theorem ifr_iff_tp2_shift (ν : Measure ℝ) [IsProbabilityMeasure ν] (ψ : ℝ → ℝ)
    (hψ : IsRegDensity ν ψ) :
    IsIFR ν ψ ↔ IsTP2On (fun ξ θ => survival ν (ξ - θ)) Set.univ Set.univ := by sorry

end LariviereIGFR.Char
