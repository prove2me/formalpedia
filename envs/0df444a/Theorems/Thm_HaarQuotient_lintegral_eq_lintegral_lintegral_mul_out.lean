-- Prove2me | Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
-- name    : HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/f563427e-17ef-5848-b3ee-566948cce057
-- title:
--   Unfolding a left invariant measure along a closed unimodular subgroup
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group, locally compact and second countable, equipped with its Borel $\sigma$-algebra (measurable space with `BorelSpace G`). Let $\mu$ be an s-finite left invariant measure on $G$, let $H$ be a subgroup whose underlying set is closed, and let $\mu_H$ be a Haar measure on $H$ that is in addition right invariant (so $H$ is unimodular). Let $f \colon G \to [0,\infty]$ be measurable. The assertion is that
--   $$\int_G^- f \, d\mu = \int_{q}^- \Big( \int_{x \in H}^- f(x \cdot q.\mathrm{out}) \, d\mu_H \Big) \, d\nu(q),$$
--   the outer integral being over the orbit space `MulAction.orbitRel.Quotient H G` of the left translation action of $H$ on $G$, i.e. the space of right cosets $Hg$, and $q.\mathrm{out}$ a chosen representative of $q$. Here $\nu$ is [`HaarQuotient.measure μ H μH`](def/HaarQuotient.html#L28), the pushforward along the quotient map $G \to H \backslash G$ of $\mu$ weighted by the density $g \mapsto \mathrm{weight}(g) / \int_{x \in H}^- \mathrm{weight}(x g) \, d\mu_H$, where $\mathrm{weight}$ is the project's function [`HaarQuotient.weight`](def/HaarQuotient.html#L12) attached to $H$ and $\mu_H$. Both sides are allowed to be $+\infty$; all integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions.
--
--   This is Weil's integration formula for the quotient of a locally compact group by a closed unimodular subgroup, in the form where the quotient measure is produced by an explicit normalised density rather than characterised abstractly, so that the formula holds with constant $1$ for that particular measure. It is the basic tool for passing between integrals over an adelic group and sums or integrals over coset spaces, and is invoked throughout the analytic estimates on automorphic forms, for instance in the bounds on class sums over double cosets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out.lean

import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂μ = ∫⁻ q, (∫⁻ x, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by sorry
