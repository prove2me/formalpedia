-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_globalPointsGL_mul
-- name    : LanglandsTunnell.CubicInduction.AdelicEpstein.epsteinPlus_globalPointsGL_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/f2ecf5d8-218f-521d-9679-98249f5a66be
-- title:
--   Left GL₃(ℚ)-invariance of the adelic Epstein integral
-- statement:
--   Work over $\mathbb{Q}$ with its ring of integers, write $\mathbb{A}$ for the adele ring and $\widehat{\mathbb{Z}}^{\times}$ for the subgroup [`IsDedekindDomain.FiniteAdeleRing.unitIdeles`](def/IsDedekindDomain_FiniteUnitIdeles.html#L9) of the units of the finite adele ring consisting of those $\delta$ for which both $\delta$ and $\delta^{-1}$ have all local components in $v$-adic integers at every height-one prime $v$. Fix a measurable space structure on $\widehat{\mathbb{Z}}^{\times}$ and an arbitrary measure $du$ on it, an arbitrary function $\Phi : \mathbb{A}^3 \to \mathbb{C}$ (no measurability, integrability or decay being assumed), a real number $\sigma$, an element $\gamma \in \mathrm{GL}_3(\mathbb{Q})$ and an element $g \in \mathrm{GL}_3(\mathbb{A})$. Here `epsteinPlus du Φ σ g` denotes the $[0,\infty]$-valued quantity $\mathrm{ofReal}\big(\|\det g\|^{\sigma}\big)$ — the idele norm being the value of the distributive Haar character of $\mathbb{A}$ — multiplied by the lower Lebesgue integral over $t$, with respect to Lebesgue measure on $(0,\infty)$ twisted by the density $t^{-1}$, of $\mathrm{ofReal}(t^{3\sigma})$ times the lower integral over $u \in \widehat{\mathbb{Z}}^{\times}$ against $du$ of $\sum_{\xi} \|\Phi(\mathrm{point}\, t\, u\, g\, \xi)\|$, the sum running over all nonzero $\xi \in \mathbb{Q}^3$, where $\mathrm{point}\, t\, u\, g\, \xi$ is the adelic vector obtained by scaling $\xi g$, embedded in $\mathbb{A}^3$, by the idele with archimedean component $t$ and finite part $u$. The assertion is that replacing $g$ by the product of the image of $\gamma$ under the entrywise map $\mathrm{GL}_3(\mathbb{Q}) \to \mathrm{GL}_3(\mathbb{A})$ induced by $\mathbb{Q} \to \mathbb{A}$ with $g$ leaves this quantity unchanged.
--
--   This is the left invariance of the adelic Epstein integral attached to $\mathrm{GL}_3$ under the group of rational points, the property which makes it a function on the quotient $\mathrm{GL}_3(\mathbb{Q}) \backslash \mathrm{GL}_3(\mathbb{A})$. It is used in the convergence and decay estimates for this integral within the cubic-induction construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_globalPointsGL_mul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.AdelicEpstein.epsteinPlus_globalPointsGL_mul
    [MeasurableSpace (IsDedekindDomain.FiniteAdeleRing.unitIdeles (NumberField.RingOfIntegers ℚ) ℚ)]
    (du : MeasureTheory.Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (NumberField.RingOfIntegers ℚ) ℚ))
    (Φ : (Fin 3 → NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) → ℂ) (σ : ℝ)
    (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (g : AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ) :
    epsteinPlus du Φ σ (globalPointsGL 3 (NumberField.RingOfIntegers ℚ) ℚ γ * g) = epsteinPlus du Φ σ g := by sorry
