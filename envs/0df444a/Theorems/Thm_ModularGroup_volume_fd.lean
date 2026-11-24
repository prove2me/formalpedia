-- Prove2me | Theorems.Thm_ModularGroup_volume_fd
-- name    : ModularGroup.volume_fd
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-24T22:33:37.05275+00:00
-- url     : https://prove2.me/theorems/4e3773de-df55-4f81-8b42-967fcb23e1f8
-- title:
--   The hyperbolic area of the standard fundamental domain of SL(2, ℤ) is π/3
-- statement:
--   Let $\mathbb{H} = \{z \in \mathbb{C} : \operatorname{Im} z > 0\}$ be the upper half-plane with the hyperbolic measure $d\mu(z) = \dfrac{dx\,dy}{y^2}$ ($z = x + iy$), and let
--
--   $$\mathcal{D} = \{z \in \mathbb{H} : |z| \ge 1,\ |\operatorname{Re} z| \le \tfrac{1}{2}\}$$
--
--   be the standard closed fundamental domain for the action of $\mathrm{SL}_2(\mathbb{Z})$ on $\mathbb{H}$ by Möbius transformations. Then
--
--   $$\mu(\mathcal{D}) = \frac{\pi}{3}.$$
--
--   This is the classical value of the hyperbolic area of the modular surface $\mathrm{SL}_2(\mathbb{Z}) \backslash \mathbb{H}$: $\int_{-1/2}^{1/2} \int_{\sqrt{1 - x^2}}^{\infty} y^{-2}\,dy\,dx = \int_{-1/2}^{1/2} \frac{dx}{\sqrt{1 - x^2}} = 2 \arcsin \tfrac{1}{2} = \frac{\pi}{3}$ (equivalently, by Gauss–Bonnet, the area of a hyperbolic triangle with angles $\pi/3, \pi/3, 0$ is $\pi - 2\pi/3$). It is the normalising constant in the Petersson inner product and in the volume terms of the Selberg and Eichler–Selberg trace formulas.
--
--   **Formalization Note**: $\mathcal{D}$ is Mathlib's `ModularGroup.fd`, the set `{z : ℍ | 1 ≤ Complex.normSq (z : ℂ) ∧ |z.re| ≤ 1 / 2}` (written `𝒟` in the `Modular` scope). The measure is Mathlib's `MeasureSpace ℍ` instance `MeasureTheory.volume` (`Mathlib.Analysis.Complex.UpperHalfPlane.Measure`): Lebesgue measure on `ℂ` pulled back to `ℍ`, with density `1 / (im z) ^ 2`. The value is stated in `ℝ≥0∞` as `ENNReal.ofReal (Real.pi / 3)`, so in particular $\mathcal{D}$ has finite hyperbolic area.
-- source:
--   Classical; see e.g. D. Zagier, The Eichler–Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Springer (1976)

import Mathlib

set_option autoImplicit false

theorem ModularGroup.volume_fd :
    MeasureTheory.volume ModularGroup.fd = ENNReal.ofReal (Real.pi / 3) := by
  sorry
