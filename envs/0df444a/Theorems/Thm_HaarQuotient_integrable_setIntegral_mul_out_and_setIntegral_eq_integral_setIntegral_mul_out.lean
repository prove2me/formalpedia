-- Prove2me | Theorems.Thm_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
-- name    : HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/adfd6bb9-4504-551e-aa3b-e45ecf4f379c
-- title:
--   Bochner quotient integral formula over a fundamental domain
-- statement:
--   Let $G$ be a group carrying a topology making it a locally compact, second countable topological group, equipped with its Borel $\sigma$-algebra, let $\mu$ be an $s$-finite left invariant measure on $G$, let $H\le G$ be a subgroup whose underlying set is closed, and let $\mu_H$ be a measure on $H$ that is both a Haar measure and right invariant. Let $\Gamma\le H$ be a countable subgroup (so $\Gamma\le G$ as well), let $f:G\to\mathbb{C}$ be measurable and satisfy $f(\gamma g)=f(g)$ for all $\gamma\in\Gamma$ and $g\in G$, let $S\subseteq G$ be a fundamental domain for the $\Gamma$-action on $G$ with respect to $\mu$, let $T\subseteq H$ be a fundamental domain for the action on $H$ of $\Gamma$ viewed as a subgroup of $H$ with respect to $\mu_H$, and assume $\int^-_S\lVert f\rVert_e\,d\mu<\infty$. Write $\nu$ for the measure on the orbit space $\mathrm{MulAction.orbitRel.Quotient}\,H\,G$ of $H$ acting on $G$ obtained by pushing forward, along the quotient map, the measure $\mu$ weighted by the density $g\mapsto \mathrm{weight}\,H\,\mu_H\,g\big/\int^-_H \mathrm{weight}\,H\,\mu_H\,(x g)\,d\mu_H(x)$, and for an orbit $q$ let $q.\mathrm{out}$ be a chosen representative in $G$. Then three assertions hold: for $\nu$-almost every $q$ the function $x\mapsto f(x\,q.\mathrm{out})$ on $H$ is integrable on $T$ with respect to $\mu_H$; the function $q\mapsto \int_T f(x\,q.\mathrm{out})\,d\mu_H(x)$ is $\nu$-integrable; and $\int_S f\,d\mu=\int \big(\int_T f(x\,q.\mathrm{out})\,d\mu_H(x)\big)\,d\nu(q)$, the integrals being Bochner integrals.
--
--   This is the Bochner (complex-valued) form of the classical quotient integration formula for a closed subgroup, here relativised to fundamental domains for a countable subgroup $\Gamma$ of $H$ on both sides; it upgrades the corresponding identity for $[0,\infty]$-valued functions, [`HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out`](thm.html#HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out), and also supplies the integrability of the fibres and of the fibre integrals. It is the unfolding device used repeatedly in the analytic theory of automorphic forms in this development, for instance in the constant-term and pseudo-Eisenstein estimates on truncated Siegel sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out.lean

import Definitions.Def_HaarQuotient
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Γ : Subgroup G) (hΓ : Γ ≤ H) [Countable Γ]
    (f : G → ℂ) (hf : Measurable f) (hfΓ : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g)
    (S : Set G) (hS : IsFundamentalDomain Γ S μ)
    (T : Set H) (hT : IsFundamentalDomain (Γ.subgroupOf H) T μH)
    (hfin : ∫⁻ g in S, ‖f g‖ₑ ∂μ < ∞) :
    (∀ᵐ q ∂(HaarQuotient.measure μ H μH), IntegrableOn (fun x : H => f ((x : G) * q.out)) T μH) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H G => ∫ x in T, f ((x : G) * q.out) ∂μH)
      (HaarQuotient.measure μ H μH) ∧
    ∫ g in S, f g ∂μ =
      ∫ q, (∫ x in T, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by sorry
