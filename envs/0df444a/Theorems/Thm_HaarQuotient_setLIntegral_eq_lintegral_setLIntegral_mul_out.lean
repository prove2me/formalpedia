-- Prove2me | Theorems.Thm_HaarQuotient_setLIntegral_eq_lintegral_setLIntegral_mul_out
-- name    : HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/def737c0-9bc7-50f7-bd26-2e969510f5ae
-- title:
--   Quotient integration formula over fundamental domains for Γ ≤ H ≤ G
-- statement:
--   Let $G$ be a group carrying a second-countable, locally compact topological group structure and its Borel $\sigma$-algebra, let $\mu$ be an $s$-finite left-invariant measure on $G$, let $H \le G$ be a subgroup whose underlying set is closed, and let $\mu_H$ be a Haar measure on $H$ that is in addition right invariant. Let $\Gamma \le H$ be a countable subgroup, let $f \colon G \to [0,\infty]$ be measurable and invariant under left translation by $\Gamma$, that is $f(\gamma g) = f(g)$ for all $\gamma \in \Gamma$ and $g \in G$, let $S \subseteq G$ be a fundamental domain, in Mathlib's almost-everywhere sense, for the left translation action of $\Gamma$ on $G$ with respect to $\mu$, and let $T \subseteq H$ be a fundamental domain for the left translation action on $H$ of $\Gamma$ regarded as a subgroup of $H$ (`Γ.subgroupOf H`) with respect to $\mu_H$. Then
--   $$\int_S f \,d\mu = \int_{q} \Big( \int_T f\big(x \cdot q.\mathrm{out}\big) \, d\mu_H(x) \Big) d\nu(q),$$
--   the outer integral being over the orbit space `MulAction.orbitRel.Quotient H G` of the left action of $H$ on $G$, i.e. the space of cosets $Hg$, with $q.\mathrm{out}$ a chosen representative of $q$ in $G$ and $x$ mapped into $G$ by the inclusion of $H$. Here $\nu$ is [`HaarQuotient.measure μ H μH`](def/HaarQuotient.html#L28), the image under the quotient map $G \to H\backslash G$ of the measure $\mu$ with density $g \mapsto \mathrm{weight}\,H\,\mu_H\,g \big/ \int_H \mathrm{weight}\,H\,\mu_H\,(x g)\, d\mu_H(x)$, where $\mathrm{weight}\,H\,\mu_H$ is the auxiliary weight function of the module. Both sides are allowed to be $+\infty$.
--
--   This is the classical quotient integration formula for a closed subgroup, in the form that computes an integral over a fundamental domain for $\Gamma$ in $G$ as an iterated integral: first over a fundamental domain for $\Gamma$ in $H$, then over the coset space $H\backslash G$ equipped with the quotient measure. In the present development it is the tool that unfolds integrals of $\Gamma$-invariant functions on $G$ in the analytic theory of automorphic forms, for instance in the estimates for pseudo-Eisenstein series and in the computation of Petersson-type integrals against Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HaarQuotient_setLIntegral_eq_lintegral_setLIntegral_mul_out.lean

import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Γ : Subgroup G) (hΓ : Γ ≤ H) [Countable Γ]
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfΓ : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g)
    (S : Set G) (hS : IsFundamentalDomain Γ S μ)
    (T : Set H) (hT : IsFundamentalDomain (Γ.subgroupOf H) T μH) :
    ∫⁻ g in S, f g ∂μ =
      ∫⁻ q, (∫⁻ x in T, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by sorry
