-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsFinIntegral_eq_const_of_ideleNorm_det_eq_one_of_nonneg
-- name    : LanglandsTunnell.RankinSelberg.exists_pos_forall_rsFinIntegral_eq_const_of_ideleNorm_det_eq_one_of_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/061e9f63-44db-50a1-ab44-3bd7a99ef90e
-- title:
--   Finite Rankin–Selberg integral constant in s and positive
-- statement:
--   Work in the group $G_f :=$ `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean component map $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q},\infty})$, equipped with the Borel structure coming from the adelic topology and assumed second countable. Let $\mu$ be a Haar measure on $G_f$, let $\mu_N$ be a Haar measure on `finUnipotent`, the subgroup of $G_f$ induced by the range of the unipotent embedding into $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and write $\nu$ for $\mu$ weighted by the density [`HaarQuotient.density finUnipotent μN`](def/HaarQuotient.html#L25) (the normalised weight function attached to a compact exhaustion). Let $W, F : G_f \to \mathbb{C}$ be functions such that: wherever $W(g)F(g) \neq 0$ the idelic norm $\mathrm{ideleNorm}_{\mathbb{Q}}(\det g)$ — the distributive Haar character of the adele ring at $\det g$ — equals $1$; every value $W(g)F(g)$ is real and non-negative; $g \mapsto W(g)F(g)$ is $\nu$-integrable; and the set where $W(g)F(g) \neq 0$ does not have $\nu$-measure zero. Then there is a real $c > 0$ such that for every $s \in \mathbb{C}$ the integral $\int_{G_f} W(g)F(g)\,\lVert\det g\rVert^{\,s-1/2}\, d\nu(g)$, i.e. `rsFinIntegral μ μN s W F`, equals $c$.
--
--   This is the degenerate case of the finite (non-archimedean) Rankin–Selberg local integral over $\mathbb{Q}$: when the integrand is concentrated on the norm-one locus of the determinant, the twisting factor $\lVert\det g\rVert^{s-1/2}$ disappears and the integral is a constant, positive function of the complex parameter. It is used in assembling the Rankin–Selberg test data over $\mathbb{Q}$, being cited by [`AutomorphicForm.exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat`](thm.html#AutomorphicForm.exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsFinIntegral_eq_const_of_ideleNorm_det_eq_one_of_nonneg.lean

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm RSCarrier

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_rsFinIntegral_eq_const_of_ideleNorm_det_eq_one_of_nonneg
    [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure finUnipotent) [μN.IsHaarMeasure]
    (W F : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hdet : ∀ g : finiteAdelicGL2Subgroup ℚ, W g * F g ≠ 0 →
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) = 1)
    (hre : ∀ g : finiteAdelicGL2Subgroup ℚ, (W g * F g).im = 0 ∧ 0 ≤ (W g * F g).re)
    (hint : Integrable (fun g : finiteAdelicGL2Subgroup ℚ => W g * F g)
      (μ.withDensity (HaarQuotient.density finUnipotent μN)))
    (hpos : (μ.withDensity (HaarQuotient.density finUnipotent μN)) {g | W g * F g ≠ 0} ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, rsFinIntegral μ μN s W F = (c : ℂ) := by sorry
