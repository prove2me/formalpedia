-- Prove2me | Theorems.Thm_HaarQuotient_setLIntegral_withDensity_eq_inv_mul_setLIntegral_of_forall_lintegral_eq
-- name    : HaarQuotient.setLIntegral_withDensity_eq_inv_mul_setLIntegral_of_forall_lintegral_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/0068ce7c-a597-5a97-9750-68bbf048352d
-- title:
--   Integral over a double coset HtK against a quotient density
-- statement:
--   Let $G$ be a topological group carrying its Borel $\sigma$-algebra, let $\mu$ be a left-invariant measure on $G$, let $H\le G$ be a subgroup equipped with a right-invariant measure $\mu_H$ on the subtype $H$, and let $\rho:G\to[0,\infty]$ be a function. Assume the quotient integration formula as a hypothesis: for every measurable $h:G\to[0,\infty]$, $\int_G h\,d\mu$ equals the integral over the orbit space of the left multiplication action of $H$ on $G$, taken against the pushforward of $\rho\,d\mu$ (the measure `μ.withDensity ρ`) along the quotient map, of $q\mapsto\int_H h(x\cdot q_{\mathrm{out}})\,d\mu_H(x)$, where $q_{\mathrm{out}}$ is the chosen representative `Quotient.out` of $q$. Let $K\le G$ be a subgroup with $K$ closed in $G$, let $t\in G$, and let $S\subseteq G$ be a measurable set whose elements are exactly the products $x t k$ with $x\in H$ and $k\in K$, i.e. $S=HtK$. Let $D\in[0,\infty]$ satisfy $D=\mu_H\{y\in H: t^{-1}yt\in K\}$ with $D\ne 0$ and $D\ne\infty$. Finally let $f:G\to[0,\infty]$ be measurable with $f(xg)=f(g)$ for all $x\in H$, $g\in G$. Then $$\int_S f\,d(\rho\,\mu)\;=\;D^{-1}\int_K f(tk)\,d\mu(k).$$ Closedness of $K$ enters only through the measurability of $K$ as a subset of $G$.
--
--   This is the unfolding of an integral over a single double coset $HtK$ of a left $H$-invariant function: relative to the quotient measure determined by the density $\rho$, such an integral reduces to an integral over the subgroup $K$, with the correction factor $D$ accounting for the $\mu_H$-mass of $\{y \in H : t^{-1}yt \in K\}$. The quotient integration formula is taken as a hypothesis, so the result is purely formal; it is used in the Rankin–Selberg local computations, in [`LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_setIntegral_translate`](thm.html#LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_setIntegral_translate).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HaarQuotient_setLIntegral_withDensity_eq_inv_mul_setLIntegral_of_forall_lintegral_eq.lean

import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

theorem HaarQuotient.setLIntegral_withDensity_eq_inv_mul_setLIntegral_of_forall_lintegral_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (H : Subgroup G) (μH : Measure ↥H) [μH.IsMulRightInvariant]
    (ρ : G → ENNReal)
    (hquot : ∀ h : G → ENNReal, Measurable h →
      ∫⁻ g, h g ∂μ = ∫⁻ q, (∫⁻ x, h ((x : G) * q.out) ∂μH)
        ∂(Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) (μ.withDensity ρ)))
    (K : Subgroup G) (hK : IsClosed (K : Set G)) (t : G) (S : Set G) (hS : MeasurableSet S)
    (hmemS : ∀ g : G, g ∈ S ↔ ∃ x ∈ H, ∃ k ∈ K, g = x * t * k)
    (D : ENNReal) (hD : μH {y : ↥H | t⁻¹ * (y : G) * t ∈ K} = D) (hD0 : D ≠ 0) (hDtop : D ≠ ⊤)
    (f : G → ENNReal) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    ∫⁻ g in S, f g ∂(μ.withDensity ρ) = D⁻¹ * ∫⁻ k in (K : Set G), f (t * k) ∂μ := by sorry
