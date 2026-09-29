-- Prove2me | Theorems.Thm_HaarQuotient_exists_lintegral_comp_mul_right_withDensity_density_eq_mul
-- name    : HaarQuotient.exists_lintegral_comp_mul_right_withDensity_density_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/5bd9da82-7466-5fdd-b40a-fd7d4a4e1fa2
-- title:
--   Right translation scales the density-weighted Haar integral
-- statement:
--   Let $G$ be a second countable, locally compact topological group with its Borel $\sigma$-algebra, $\mu$ a Haar measure on $G$, $H \le G$ a subgroup whose underlying set is closed, and $\mu_H$ a Haar measure on $H$ that is moreover right invariant; let $x \in G$. Write $D =$ [`HaarQuotient.density H μH`](def/HaarQuotient.html#L25) for the function $g \mapsto w(g)\big/\int_H w(hg)\,d\mu_H(h)$, where $w =$ [`HaarQuotient.weight H μH`](def/HaarQuotient.html#L12) is the explicit Borel weight built from a compact exhaustion $(K_n)$ of $G$, namely $w(g) = \sum_{n} 2^{-n}\,\bigl(1 + \mu_H\bigl(H \cap (K_{n+1}K_{n+1}^{-1})\bigr)\bigr)^{-1}\,\mathbf{1}_{\operatorname{int} K_{n+1}}(g)$ when $G$ is $\sigma$-compact and weakly locally compact, and $w = 0$ otherwise. The assertion is that there exists a nonzero $c \in \mathbb{R}_{\ge 0}$ such that for every measurable $\Phi : G \to [0,\infty]$ satisfying $\Phi(hg) = \Phi(g)$ for all $h \in H$, $g \in G$, one has $$\int_G \Phi(gx)\,d(D \cdot \mu)(g) = c \int_G \Phi(g)\,d(D \cdot \mu)(g),$$ the integrals being Lebesgue integrals in $[0,\infty]$ against the measure $\mu$ weighted by $D$. The constant $c$ is asserted only to exist and to be nonzero; it is not identified with the value of the modular function at $x$.
--
--   This is the measure-theoretic statement that right translation by a fixed element of $G$ rescales the quotient measure on $H \backslash G$ by a positive constant (the value of the modular function of $G$), here in the form of a scaling identity for $H$-left-invariant non-negative integrands against the density-weighted Haar measure $D \cdot \mu$, whose pushforward along $G \to H \backslash G$ is the quotient measure. It feeds the integrability criterion for right translates of such integrands, used for the Rankin–Selberg cell integrands on $\mathrm{GL}_2$ in the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HaarQuotient_exists_lintegral_comp_mul_right_withDensity_density_eq_mul.lean

import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal Pointwise

theorem HaarQuotient.exists_lintegral_comp_mul_right_withDensity_density_eq_mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (x : G) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ (Φ : G → ℝ≥0∞), Measurable Φ → (∀ (h : H) (g : G), Φ ((h : G) * g) = Φ g) →
      ∫⁻ g, Φ (g * x) ∂(μ.withDensity (HaarQuotient.density H μH)) =
        c * ∫⁻ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH)) := by sorry
