-- Prove2me | Theorems.Thm_IQCAlg_HeavyBall_spectral_radius_P
-- name    : IQCAlg.HeavyBall.spectral_radius_P
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:59.482871+00:00
-- url     : https://prove2.me/theorems/98c2d0b0-48e5-4cb4-9d19-4834ba606e41
-- title:
--   Appendix B, p. 40 — ρ(P) = 2/3
-- statement:
--   The spectral radius of
--   $$P=\begin{bmatrix}-4/3&-4/9\\1&0\end{bmatrix},$$
--   the largest modulus of its (complex) eigenvalues, equals $2/3$:
--   $$\rho(P)=\tfrac23<1 .$$
--
--   The page uses this to explain why perturbations of the cycle decay as long as the iterates stay on the cycle's pieces; the rigorous argument then goes through $\|P^8\|$.
--
--   **Formalization Note** The spectrum is taken over $\mathbb C$ (of $P$ viewed as a complex matrix), so that complex eigenvalues would be counted; the spectral radius is Mathlib's `spectralRadius`, valued in $[0,\infty]$.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 40, "It is immediate that ρ(P) = 2/3 < 1"

import Mathlib
import Definitions.Def_IQCAlg_HeavyBall_Setting

namespace IQCAlg.HeavyBall

/-- p. 40: `ρ(P) = 2/3`, the spectral radius of `P` taken over its complex eigenvalues. -/
theorem spectral_radius_P :
    spectralRadius ℂ (Pm.map (algebraMap ℝ ℂ)) = (2 / 3 : ENNReal) := by sorry

end IQCAlg.HeavyBall
