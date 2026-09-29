-- Prove2me | Theorems.Thm_HaarQuotient_exists_forall_integral_withDensity_density_eq_smul_of_isHaarMeasure
-- name    : HaarQuotient.exists_forall_integral_withDensity_density_eq_smul_of_isHaarMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/67cf4269-6e2c-5600-82d3-b07c2675af53
-- title:
--   Rescaling of quotient integrals under change of Haar normalisations
-- statement:
--   Let $G$ be a second-countable, locally compact Hausdorff topological group with its Borel $\sigma$-algebra, and let $E$ be a second-countable real Banach space with its Borel $\sigma$-algebra. Let $H$ be a subgroup of $G$ whose underlying set is closed, let $\mu,\mu'$ be Haar measures on $G$, and let $\mu_H,\mu_H'$ be Haar measures on $H$ that are in addition right invariant. For a right-invariant Haar measure $\nu$ on $H$, the function [`HaarQuotient.density H ν`](def/HaarQuotient.html#L25) sends $g\in G$ to $w_\nu(g)/\int^-_{x\in H} w_\nu(xg)\,d\nu$, where the weight $w_\nu$ is the series $\sum_n 2^{-n}\bigl(1+\nu(\iota^{-1}(K_{n+1}K_{n+1}^{-1}))\bigr)^{-1}\mathbf 1_{\operatorname{int}K_{n+1}}(g)$ built from a chosen compact exhaustion $(K_n)$ of $G$ and the inclusion $\iota\colon H\to G$ (and is $0$ unless $G$ is $\sigma$-compact and weakly locally compact). The assertion is the existence of a nonzero constant $c\in\mathbb R_{\ge 0}$, independent of everything below, such that for every function $\Phi\colon G\to E$ satisfying $\Phi(hg)=\Phi(g)$ for all $h\in H$ and $g\in G$ one has $\int_G\Phi\,d\bigl(\mu'\cdot\mathrm{density}\,H\,\mu_H'\bigr)=c\cdot\int_G\Phi\,d\bigl(\mu\cdot\mathrm{density}\,H\,\mu_H\bigr)$, the measures being the given Haar measures weighted by the respective densities. No measurability or integrability hypothesis on $\Phi$ is imposed.
--
--   Both sides are realisations of the integral of an $H$-left-invariant function over the quotient $H\backslash G$ against the quotient measures attached to the pairs $(\mu',\mu_H')$ and $(\mu,\mu_H)$, and the statement is the uniqueness-of-Haar-measure comparison of these two normalisations, in the form of a single positive proportionality constant valid for all invariant integrands simultaneously. It is used in the Rankin–Selberg part of the Langlands–Tunnell input, where global zeta integrals are compared after changing the Haar normalisations used to define local and global integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HaarQuotient_exists_forall_integral_withDensity_density_eq_smul_of_isHaarMeasure.lean

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

theorem HaarQuotient.exists_forall_integral_withDensity_density_eq_smul_of_isHaarMeasure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure]
    (μH μH' : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    [μH'.IsHaarMeasure] [μH'.IsMulRightInvariant] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ (Φ : G → E), (∀ (h : H) (g : G), Φ ((h : G) * g) = Φ g) →
      (∫ g, Φ g ∂(μ'.withDensity (HaarQuotient.density H μH'))) =
        (c : ℝ) • ∫ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH)) := by sorry
