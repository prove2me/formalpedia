-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_adelicUnipotent_lintegral_indicator_slab_mul_density_centralScalar_inv_mul_eq
-- name    : LanglandsTunnell.RankinSelberg.exists_pos_forall_lintegral_adelicUnipotent_lintegral_indicator_slab_mul_density_centralScalar_inv_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/c757978e-3b5d-510b-a401-56907cd6bf7d
-- title:
--   Central average of the quotient density over a norm slab
-- statement:
--   Let $F$ be a number field, with the adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F` and $\mathrm{GL}_2(\mathbb{A}_F)$ carrying their Borel $\sigma$-algebras, and let the idele group $\mathbb{A}_F^\times$ carry a measurable structure that is Borel for its topology. Let $\nu_0$ be a Haar measure on $\mathbb{A}_F^\times$ and let $e_1 < e_2$ be reals with $0 < e_1$. The assertion is that there exists a real $C > 0$ such that for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ the iterated lower Lebesgue integral
--   $$\int_{N(\mathbb{A}_F)} \int_{\mathbb{A}_F^\times} \mathbf{1}_S\big(z_t^{-1} n g\big)\,\rho\big(z_t^{-1} n g\big)\, \mathrm{d}\nu_0(t)\, \mathrm{d}n$$
--   equals `ENNReal.ofReal C`. Here $N(\mathbb{A}_F)$ is `adelicUnipotent F`, the range of $x \mapsto \begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$ on $\mathbb{A}_F$, integrated against `unipotentHaar F`, the image under that map of the additive adelic Haar measure rescaled so that the adelic box has measure $1$; $z_t = \mathrm{diag}(t,t)$ is `centralScalar (𝓞 F) F t`; $S$ is the set of $x \in \mathrm{GL}_2(\mathbb{A}_F)$ with $\|\det x\| \in [e_1,e_2]$, the norm being `ideleNorm F`, the value at $\det x$ of the distributive Haar character of $\mathbb{A}_F$ read as a real number; and $\rho$ is [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the subgroup $Z(F)N(\mathbb{A}_F) =$ `rationalCentreUnipotent F`, the join of the range of $a \mapsto \mathrm{diag}(a,a)$ on $F^\times$ with $N(\mathbb{A}_F)$, taken with respect to `rationalCentreUnipotentHaar F`, the sum over $a \in F^\times$ of the translates by $\mathrm{diag}(a,a)$ of `unipotentHaar F`; by definition $\rho(y)$ is the value of `weight` at $y$ divided by the integral of $x \mapsto$ `weight` at $xy$ over the subgroup.
--
--   This is the centre-averaging step in the Godement–Jacquet style unfolding of the global $\mathrm{GL}_2 \times \mathrm{GL}_2$ Rankin–Selberg integral: averaging the indicator of a determinant-norm slab against the quotient density of $Z(F)N(\mathbb{A}_F)$ over the centre and the unipotent radical produces a constant independent of $g$. It is used in the construction of the Rankin–Selberg integral over the $Z(F)N(\mathbb{A}_F)$-quotient, where the resulting constant is compared with a Whittaker integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_adelicUnipotent_lintegral_indicator_slab_mul_density_centralScalar_inv_mul_eq.lean

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicFourier IsDedekindDomain
open NumberField.TateGlobal
open AutomorphicForm LanglandsTunnell.RankinSelberg
open scoped ENNReal

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_lintegral_adelicUnipotent_lintegral_indicator_slab_mul_density_centralScalar_inv_mul_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : AdelicGL2 (𝓞 F) F,
      ∫⁻ n : adelicUnipotent F,
        (∫⁻ t : (AdeleRing (𝓞 F) F)ˣ,
            {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc e₁ e₂}.indicator
                (HaarQuotient.density (rationalCentreUnipotent F) (rationalCentreUnipotentHaar F))
              ((centralScalar (𝓞 F) F t)⁻¹ * ((n : AdelicGL2 (𝓞 F) F) * g)) ∂ν₀)
        ∂(unipotentHaar F) = ENNReal.ofReal C := by sorry
