-- Prove2me | Theorems.Thm_HaarQuotient_lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top
-- name    : HaarQuotient.lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/360e11a9-e1ed-5de0-ae67-0bb47328ec31
-- title:
--   Measure of H· K for the pinned orbit density
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group which is locally compact and second countable, equipped with its Borel $\sigma$-algebra, and let $\mu$ be a Haar measure on $G$. Let $H\le G$ be a subgroup whose underlying set is closed, and let $\mu_H$ be a Haar measure on $H$ which is in addition right invariant. Let $K\le G$ be a subgroup whose underlying set is both open and compact. Write $D=$ [`HaarQuotient.density H μH`](def/HaarQuotient.html#L25), the function $g\mapsto w(g)\big/\int^-_{x\in H} w(xg)\,d\mu_H$, where $w=$ [`HaarQuotient.weight H μH`](def/HaarQuotient.html#L12) is, when $G$ is $\sigma$-compact and weakly locally compact, the function $g\mapsto \sum_{n\ge 0} 2^{-n}\bigl(1+\mu_H(\iota^{-1}(C_{n+1}C_{n+1}^{-1}))\bigr)^{-1}\mathbf 1_{\operatorname{int} C_{n+1}}(g)$ for $C_n$ the $n$-th term of a chosen compact exhaustion of $G$ and $\iota\colon H\to G$ the inclusion, and is $0$ otherwise. The assertion is the conjunction of two statements about the lower Lebesgue integral of the $\{0,1\}$-valued indicator of the set product $H\cdot K\subseteq G$ against the measure $\mu$ weighted by the density $D$: this integral equals $\mu(K)/\mu_H(\iota^{-1}(K))$, and it is finite.
--
--   The set $H\cdot K$ is the union of the $H$-orbits meeting $K$, so the statement computes the quotient (Weil) measure of the image of the double coset $H\cdot K$ in $H\backslash G$ as $\mu(K)/\mu_H(H\cap K)$, a finite quantity since $K$ is compact and $H\cap K$ is open and non-empty in $H$. It underlies the finiteness lemma [`HaarQuotient.withDensity_density_coe_mul_lt_top_of_isCompact`](thm.html#HaarQuotient.withDensity_density_coe_mul_lt_top_of_isCompact) and is used in the integrability estimates for Rankin–Selberg integrals in the Langlands–Tunnell part of the development, where $H$ is a unipotent subgroup and $K$ a compact open subgroup of $\mathrm{GL}_2$ over a non-archimedean local field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HaarQuotient_lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top.lean

import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal Pointwise

theorem HaarQuotient.lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) :
    ∫⁻ g, ((H : Set G) * (K : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g ∂(μ.withDensity (HaarQuotient.density H μH)) =
        μ K / μH (((↑) : H → G) ⁻¹' (K : Set G)) ∧
      ∫⁻ g, ((H : Set G) * (K : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g ∂(μ.withDensity (HaarQuotient.density H μH)) < ⊤ := by sorry
