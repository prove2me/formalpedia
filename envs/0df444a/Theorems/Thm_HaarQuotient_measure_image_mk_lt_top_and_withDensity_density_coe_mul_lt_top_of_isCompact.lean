-- Prove2me | Theorems.Thm_HaarQuotient_measure_image_mk_lt_top_and_withDensity_density_coe_mul_lt_top_of_isCompact
-- name    : HaarQuotient.measure_image_mk_lt_top_and_withDensity_density_coe_mul_lt_top_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/ee6e0d4e-6847-561c-b7f6-38d412d9e5d7
-- title:
--   Compact sets have finite Haar quotient measure
-- statement:
--   Let $G$ be a group carrying a second-countable, locally compact topological group structure whose measurable structure is the Borel one, let $\mu$ be a Haar measure on $G$, let $H \le G$ be a subgroup whose underlying set is closed, and let $\mu_H$ be a measure on $H$ that is both a Haar measure and right invariant. Let $K \subseteq G$ be compact. Write $\rho =$ [`HaarQuotient.density H μH`](def/HaarQuotient.html#L25) for the function $g \mapsto w(g) / \int^-_{x : H} w(xg)\,d\mu_H$, where $w =$ [`HaarQuotient.weight H μH`](def/HaarQuotient.html#L12) is, when $G$ is $\sigma$-compact and weakly locally compact, the sum $\sum_n 2^{-n}\bigl(1 + \mu_H(\iota^{-1}(C_{n+1} C_{n+1}^{-1}))\bigr)^{-1}\,\mathbf{1}_{\operatorname{int} C_{n+1}}$ for the chosen compact exhaustion $(C_n)$ of $G$ and $\iota : H \to G$ the inclusion, and $0$ otherwise; and let [`HaarQuotient.measure μ H μH`](def/HaarQuotient.html#L28) be the push-forward of $\mu.\mathrm{withDensity}\,\rho$ along the quotient map $G \to$ `MulAction.orbitRel.Quotient H G`. The assertion is the conjunction: the image of $K$ in the quotient has [`HaarQuotient.measure μ H μH`](def/HaarQuotient.html#L28)-measure $< \infty$, and the set $H \cdot K$ has $\mu.\mathrm{withDensity}\,\rho$-measure $< \infty$.
--
--   This is the finiteness statement that makes the quotient measure on $H \backslash G$ built from the density $\rho$ usable as a measure for integration: compacta downstairs have finite mass, and so do their saturations upstairs. It is invoked to justify absolute convergence in the unfolding of orbital and twisted orbital integrals and in the idelic descent computations of the automorphic side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HaarQuotient_measure_image_mk_lt_top_and_withDensity_density_coe_mul_lt_top_of_isCompact.lean

import Definitions.Def_HaarQuotient
import Mathlib.MeasureTheory.Measure.Haar.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Pointwise

theorem HaarQuotient.measure_image_mk_lt_top_and_withDensity_density_coe_mul_lt_top_of_isCompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (K : Set G) (hK : IsCompact K) :
    HaarQuotient.measure μ H μH ((Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) '' K) < ⊤ ∧
    (μ.withDensity (HaarQuotient.density H μH)) ((H : Set G) * K) < ⊤ := by sorry
