-- Prove2me | Theorems.Thm_HaarQuotient_map_mk_withDensity_eq_smul_measure
-- name    : HaarQuotient.map_mk_withDensity_eq_smul_measure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/cbf40c15-8a30-5e5f-8c1e-5a2d97e9ccb2
-- title:
--   Pushforward of a density with constant coset integral
-- statement:
--   Let $G$ be a group carrying a topology making it a locally compact, second countable topological group, equipped with its Borel $\sigma$-algebra, let $\mu$ be an s-finite left-invariant measure on $G$, let $H$ be a subgroup of $G$ whose underlying set is closed, and let $\mu_H$ be a measure on $H$ that is a Haar measure and is in addition right invariant. Let $\rho\colon G\to[0,\infty]$ be measurable and let $c\in[0,\infty]$ be such that for every $g\in G$ one has $\int_H \rho((x:G)\,g)\,d\mu_H(x)=c$, i.e. the integral of $\rho$ over each orbit of $H$ is the same value $c$. Then the image of the measure $\rho\cdot\mu$ under the quotient map $G\to$ `MulAction.orbitRel.Quotient H G` onto the orbit space of $H$ acting on $G$ equals $c$ times [`HaarQuotient.measure μ H μH`](def/HaarQuotient.html#L28), the latter being by definition the image of $\mu$ weighted by the density $g\mapsto w(g)/\int_H w((x:G)\,g)\,d\mu_H(x)$, where $w$ denotes [`HaarQuotient.weight H μH`](def/HaarQuotient.html#L12).
--
--   This is the uniqueness, up to a scalar, of the quotient measure on $H\backslash G$ attached to Weil's integration formula: any weight whose integral along every orbit is a constant $c$ pushes $\mu$ forward to $c$ times the normalised quotient measure. It is used to compare different constructions of integrals over quotients such as $N\backslash \mathrm{GL}_2$, and is invoked by the lemmas on integration against `withDensity` of the quotient density, including the change of variables along a multiplicative equivalence and along right translation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HaarQuotient_map_mk_withDensity_eq_smul_measure.lean

import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem HaarQuotient.map_mk_withDensity_eq_smul_measure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (c : ℝ≥0∞)
    (hρc : ∀ g : G, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = c) :
    Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) (μ.withDensity ρ) =
      c • HaarQuotient.measure μ H μH := by sorry
