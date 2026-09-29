-- Prove2me | Theorems.Thm_HaarQuotient_integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
-- name    : HaarQuotient.integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/0119daca-b83b-59b3-be21-c8a7a183df12
-- title:
--   Quotient integral formula for complex integrable functions
-- statement:
--   Let $G$ be a group carrying a topology making it a second-countable, locally compact topological group, with the Borel $\sigma$-algebra, let $\mu$ be an $s$-finite left-invariant measure on $G$, let $H$ be a subgroup whose underlying set is closed, and let $\mu_H$ be a right-invariant Haar measure on $H$. Let $f\colon G\to\mathbb{C}$ be measurable with $\int^{-}\|f(g)\|_e\,d\mu(g)<\infty$, the lower Lebesgue integral of the extended-real-valued norm being finite. Here the quotient $H\backslash G$ is realised as the quotient of $G$ by the orbit relation of the multiplication action of $H$, and it is equipped with the measure [`HaarQuotient.measure`](def/HaarQuotient.html#L28) $\mu$ $H$ $\mu_H$, that is, the pushforward along the quotient map of $\mu$ weighted by the density $g\mapsto \mathrm{weight}\,H\,\mu_H\,g \big/ \int^{-}_{x\in H}\mathrm{weight}\,H\,\mu_H\,(xg)\,d\mu_H$, where `weight H μH` is the auxiliary weight function attached to $H$ and $\mu_H$. The conclusion is the conjunction of three assertions: for almost every coset $q$, the function $x\mapsto f(x\cdot q.\mathrm{out})$ on $H$ is Bochner integrable for $\mu_H$, where $q.\mathrm{out}$ is a chosen representative of $q$; the fibre integral $q\mapsto\int_{x\in H} f(x\cdot q.\mathrm{out})\,d\mu_H$ is integrable on $H\backslash G$ for that quotient measure; and $$\int_G f\,d\mu=\int_{H\backslash G}\Big(\int_{x\in H} f(x\cdot q.\mathrm{out})\,d\mu_H\Big)\,dq.$$
--
--   This is the Weil quotient (Fubini) formula for a closed subgroup, in the Bochner-integral form for complex-valued integrable functions, the counterpart of the corresponding identity for lower Lebesgue integrals of $[0,\infty]$-valued functions, which the proof cites. It is the basic tool for unfolding integrals over a group into fibre integrals over a closed subgroup and is used in the computations of orbital and twisted orbital integrals and in the unfolding of central characters for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HaarQuotient_integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out.lean

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem HaarQuotient.integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℂ) (hf : Measurable f) (hfi : ∫⁻ g, ‖f g‖ₑ ∂μ < ∞) :
    (∀ᵐ q ∂(HaarQuotient.measure μ H μH), Integrable (fun x : H => f ((x : G) * q.out)) μH) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H G => (∫ x : H, f ((x : G) * q.out) ∂μH))
      (HaarQuotient.measure μ H μH) ∧
    ∫ g, f g ∂μ = ∫ q, (∫ x : H, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by sorry
