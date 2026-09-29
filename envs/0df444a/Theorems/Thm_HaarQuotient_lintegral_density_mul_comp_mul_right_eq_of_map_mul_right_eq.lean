-- Prove2me | Theorems.Thm_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq
-- name    : HaarQuotient.lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/58786125-9f93-5e7d-adbf-9bc7a3d3c20e
-- title:
--   Right translation invariance of the density-weighted integral
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group, locally compact, second countable, with a measurable structure which is the Borel structure of the topology. Let $\mu$ be a left-invariant $s$-finite measure on $G$, let $H$ be a subgroup of $G$ whose underlying set is closed, and let $\mu_H$ be an $s$-finite measure on $H$ that is a Haar measure and is moreover right invariant. Let $f : G \to [0,\infty]$ be measurable and satisfy $f(xg) = f(g)$ for all $x \in H$ and all $g \in G$, and let $h \in G$ be such that the pushforward of $\mu$ along $g \mapsto g h$ is again $\mu$. Write $\mathrm{density}\,H\,\mu_H$ for the function $g \mapsto w(g) / \int_{H}^{-} w(xg)\,d\mu_H(x)$, where $w = \mathrm{weight}\,H\,\mu_H$ is the function defined, when $G$ is $\sigma$-compact and weakly locally compact, by the series $\sum_{n} 2^{-n} \bigl(1 + \mu_H(\iota^{-1}(K_{n+1} K_{n+1}^{-1}))\bigr)^{-1} \mathbf{1}_{\mathrm{int}\,K_{n+1}}$ with $(K_n)$ a chosen compact exhaustion of $G$ and $\iota : H \to G$ the inclusion, and by $0$ otherwise. Then the lower Lebesgue integrals satisfy $$\int^{-}_{G} \mathrm{density}\,H\,\mu_H(g)\, f(gh)\,d\mu(g) \;=\; \int^{-}_{G} \mathrm{density}\,H\,\mu_H(g)\, f(g)\,d\mu(g).$$
--
--   This is the right-translation invariance, for one fixed element $h$ preserving $\mu$, of the integral over $G$ of a left-$H$-invariant function weighted by the density used to realise the quotient measure on $H \backslash G$; classically it reflects the fact that such an integral is really an integral over the coset space. It is used for the corresponding statement about functions pulled back from the quotient via coset representatives, and downstream in the Rankin–Selberg unfolding computations of the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq.lean

import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

theorem HaarQuotient.lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] [SFinite μH]
    (f : G → ENNReal) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) (h : G)
    (hμh : Measure.map (· * h) μ = μ) :
    ∫⁻ g, HaarQuotient.density H μH g * f (g * h) ∂μ = ∫⁻ g, HaarQuotient.density H μH g * f g ∂μ := by sorry
