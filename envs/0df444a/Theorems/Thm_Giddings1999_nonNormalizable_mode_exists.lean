-- Prove2me | Theorems.Thm_Giddings1999_nonNormalizable_mode_exists
-- name    : Giddings1999.nonNormalizable_mode_exists
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T01:50:51.070671+00:00
-- url     : https://prove2.me/theorems/65cf22a0-3246-4768-a868-025ddcf5f86f
-- title:
--   Eqs. (8)–(9): off the spectrum, a regular solution with $\chi_{\omega l}\sim(\cos r)^{2h_-}$ exists
-- statement:
--   Let $d\ge2$, $R>0$, $m\in\mathbb R$, $l\in\mathbb N$, and let $\omega\in\mathbb R$ satisfy $|\omega|\neq\omega_{nl}$ for every $n\in\mathbb N$. Then there is a solution $\chi_{\omega l}$ of the radial equation at frequency $\omega$ that is bounded near $r=0$ and satisfies
--   $$\lim_{r\to\pi/2^-}\frac{\chi_{\omega l}(r)}{(\cos r)^{2h_-}}=1 .$$
--
--   These are the non-normalizable modes $\phi_{\omega l\vec m}=e^{-i\omega t}Y_{l\vec m}\chi_{\omega l}$ of eq. (8), in the normalization convention of eq. (9).
--
--   **Formalization Note** The paper says these solutions exist "at arbitrary frequency". At $|\omega|=\omega_{nl}$ the solution that is regular at $r=0$ is the normalizable $\chi_{nl}$, so the coefficient of $(\cos r)^{2h_-}$ cannot be normalized to $1$. The statement therefore excludes the spectrum.
-- source:
--   S. B. Giddings, Boundary S matrix and the anti-de Sitter space to conformal field theory dictionary, Phys. Rev. Lett. 83, 2707 (1999), https://doi.org/10.1103/PhysRevLett.83.2707, eqs. (8), (9), p. 2707

import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Filter Topology

namespace Giddings1999

/-- **Milestone, eqs. (8), (9)**: away from the normalizable spectrum, there is a solution regular at
the origin with boundary behaviour `χ_{ωl}(r) → (cos r)^{2h₋}` (normalized coefficient `1`). -/
theorem nonNormalizable_mode_exists (d : ℕ) (hd : 2 ≤ d) (m R : ℝ) (hR : 0 < R) (ω : ℝ) (l : ℕ)
    (hω : ∀ n : ℕ, |ω| ≠ omegaNL d m R n l) :
    ∃ χ : ℝ → ℝ, IsRadialSolution d m R ω l χ ∧ IsRegularAtOrigin χ ∧
      Tendsto (fun r => χ r / cos r ^ twoHMinus d m R) (𝓝[<] (π / 2)) (𝓝 1) := by
  sorry

end Giddings1999
