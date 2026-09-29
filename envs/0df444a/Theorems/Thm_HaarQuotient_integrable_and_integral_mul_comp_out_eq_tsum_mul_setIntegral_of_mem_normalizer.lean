-- Prove2me | Theorems.Thm_HaarQuotient_integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer
-- name    : HaarQuotient.integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/ae2fa06a-d2a6-58bf-b3c7-20cad82b622e
-- title:
--   Complex shell-peeling identity for integrals over Hbackslash G
-- statement:
--   Let $G$ be a group carrying a topology making it a locally compact, second countable topological group, with its Borel $\sigma$-algebra, let $\mu$ be an s-finite left-invariant measure on $G$, let $H$ be a subgroup whose underlying set is closed, and let $\mu_H$ be a measure on $H$ that is both a Haar measure and right invariant. Write $\nu$ for the quotient measure [`HaarQuotient.measure μ H μH`](def/HaarQuotient.html#L28) on the orbit space $H\backslash G$ of the left translation action, i.e. the pushforward along $g \mapsto Hg$ of $\mu$ weighted by the density $g \mapsto \mathrm{weight}(g)/\int_H \mathrm{weight}(xg)\,d\mu_H(x)$, and let $q \mapsto q.\mathrm{out}$ denote the choice of representative in $G$ of a coset $q$. Assume given $b \in G$ with $y \in H \iff byb^{-1} \in H$ for all $y \in G$, and a constant $D \in \mathbb{R}_{\ge 0}$, $D \ne 0$, such that $\int_H F(bxb^{-1})\,d\mu_H(x) = D\int_H F\,d\mu_H$ for every measurable $F : H \to [0,\infty]$. Assume $m : G \to \mathbb{Z}$ is measurable with $m(xg) = m(g)$ for $x \in H$ and $m(bg) = m(g)+1$; $h : G \to \mathbb{C}$ is measurable with $h(xg) = h(g)$ for $x \in H$ and $h(bg) = h(g)$; the function $q \mapsto h(q.\mathrm{out})$ is integrable on the zeroth shell $\{q : m(q.\mathrm{out}) = 0\}$ with respect to $\nu$; and $\Phi : \mathbb{Z} \to \mathbb{C}$ satisfies $\sum_{n \in \mathbb{Z}} D^n\|\Phi(n)\| < \infty$. Then the conclusion is the conjunction: $q \mapsto h(q.\mathrm{out})\,\Phi(m(q.\mathrm{out}))$ is $\nu$-integrable, and $$\int_{H\backslash G} h(q.\mathrm{out})\,\Phi(m(q.\mathrm{out}))\,d\nu(q) = \Big(\sum_{n \in \mathbb{Z}} D^n\,\Phi(n)\Big)\int_{\{q\,:\,m(q.\mathrm{out})=0\}} h(q.\mathrm{out})\,d\nu(q).$$
--
--   This is the complex-valued, Bochner-integral form of the shell-peeling computation for integrals over $H\backslash G$: the level sets of $m$ are permuted by left translation by the normalising element $b$, which scales the quotient measure by $D$, so the whole integral factors as a geometric-type series in $D$ times the integral over the zeroth shell. It is obtained from the $[0,\infty]$-valued identity [`HaarQuotient.lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer`](thm.html#HaarQuotient.lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer) together with the translation relation [`HaarQuotient.lintegral_comp_inv_mul_out_eq_mul_lintegral_of_mem_normalizer`](thm.html#HaarQuotient.lintegral_comp_inv_mul_out_eq_mul_lintegral_of_mem_normalizer), and it feeds the unfolding of Rankin–Selberg integrals into shell contributions in [`AutomorphicForm.RankinSelberg.exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion`](thm.html#AutomorphicForm.RankinSelberg.exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HaarQuotient_integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer.lean

import Mathlib
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

theorem HaarQuotient.integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) (D : ℝ≥0) (hD₀ : D ≠ 0)
    (hbD : ∀ F : H → ℝ≥0∞, Measurable F →
      ∫⁻ x, F ⟨b * (x : G) * b⁻¹, (hb (x : G)).mp x.2⟩ ∂μH = (D : ℝ≥0∞) * ∫⁻ x, F x ∂μH)
    (m : G → ℤ) (hm : Measurable m) (hmH : ∀ x ∈ H, ∀ g : G, m (x * g) = m g)
    (hmb : ∀ g : G, m (b * g) = m g + 1)
    (h : G → ℂ) (hh : Measurable h) (hhH : ∀ x ∈ H, ∀ g : G, h (x * g) = h g)
    (hhb : ∀ g : G, h (b * g) = h g)
    (hint : IntegrableOn (fun q : MulAction.orbitRel.Quotient H G => h q.out)
      {q : MulAction.orbitRel.Quotient H G | m q.out = 0} (HaarQuotient.measure μ H μH))
    (Φ : ℤ → ℂ) (hΦ : Summable fun n : ℤ => (D : ℝ) ^ n * ‖Φ n‖) :
    Integrable (fun q : MulAction.orbitRel.Quotient H G => h q.out * Φ (m q.out)) (HaarQuotient.measure μ H μH) ∧
    (∫ q, h q.out * Φ (m q.out) ∂(HaarQuotient.measure μ H μH)) =
      (∑' n : ℤ, ((D : ℝ) : ℂ) ^ n * Φ n) *
        ∫ q in {q : MulAction.orbitRel.Quotient H G | m q.out = 0}, h q.out ∂(HaarQuotient.measure μ H μH) := by sorry
