-- Prove2me | Theorems.Thm_HolographicQuantumMatter_power_law_solution_iff
-- name    : HolographicQuantumMatter.power_law_solution_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T17:44:30.125849+00:00
-- url     : https://prove2.me/theorems/448639e3-b196-45b4-8e02-72bcaa2fdcd4
-- title:
--   Mass–dimension relation $\Delta(\Delta-d-1)=(mL)^2$ (eq. 29)
-- statement:
--   Let $d\ge 0$ be the number of boundary spatial dimensions, $L>0$ the AdS radius and $m^2\in\mathbb R$ the mass squared of a bulk scalar in Poincaré $\mathrm{AdS}_{d+2}$. At zero frequency and zero momentum ($\omega=k=0$) the radial equation (27) reads
--
--   $$\phi''(r)-\frac{d}{r}\,\phi'(r)-\frac{m^2L^2}{r^2}\,\phi(r)=0,\qquad r>0.$$
--
--   For every real exponent $\Delta$, the power law $\phi(r)=r^{\Delta}$ solves this equation on $r>0$ if and only if
--
--   $$\Delta(\Delta-d-1)=m^2L^2 .$$
--
--   This is the relation (29) between the bulk mass and the scaling dimension $\Delta$ of the dual operator, obtained from the leading power behaviour of solutions near the boundary $r\to0$.
--
--   **Formalization Note** The boundary theory has $d$ spatial dimensions (so the bulk is $\mathrm{AdS}_{d+2}$), following the source's convention. The bulk mass squared is a real parameter $m^2$ (called `msq`), allowed to be negative; the source writes $(mL)^2$ for $m^2L^2$. Fields are real-valued functions of $r$; only their values on $r>0$ matter. The frequency/momentum terms are set to zero, which is where the power laws in (28) are exact solutions.
-- source:
--   Hartnoll, Lucas, Sachdev, *Holographic quantum matter*, arXiv:1612.07324v3, https://arxiv.org/abs/1612.07324, Section 1.6.2, p. 10, eqs. (27)–(29)

import Mathlib
import Definitions.Def_HolographicQuantumMatter_ScalarAdS

namespace HolographicQuantumMatter

theorem power_law_solution_iff (d : ℕ) (msq L : ℝ) (hL : 0 < L) (Δ : ℝ) :
    IsRadialSolution d 0 0 msq L (fun r => r ^ Δ) ↔
      Δ * (Δ - ((d : ℝ) + 1)) = msq * L ^ 2 := by sorry

end HolographicQuantumMatter
