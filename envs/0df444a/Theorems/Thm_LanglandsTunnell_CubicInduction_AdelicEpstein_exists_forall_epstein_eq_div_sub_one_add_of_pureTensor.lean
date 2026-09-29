-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_exists_forall_epstein_eq_div_sub_one_add_of_pureTensor
-- name    : LanglandsTunnell.CubicInduction.AdelicEpstein.exists_forall_epstein_eq_div_sub_one_add_of_pureTensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/55e36de7-6de0-5844-ae04-b9579821aa67
-- title:
--   Simple pole at σ=1 of the adelic Epstein integral on GL₃
-- statement:
--   Fix a $\sigma$-algebra on the group $\hat{\mathbb Z}^\times =$ [`IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ`](def/IsDedekindDomain_FiniteUnitIdeles.html#L9) of finite ideles of $\mathbb Q$ whose components and inverse components are all integral, and assume (`hmeas`) that $u \mapsto$ `finUnitIdele u`, the idele of $\mathbb A =$ `AdeleRing (𝓞 ℚ) ℚ` obtained by pushing $u$ forward along the inclusion of the finite adeles (trivial archimedean part), is measurable for the Borel $\sigma$-algebra [`NumberField.AdelicHaar.adeleBorel`](def/NumberField_AdelicHaar.html#L132) of $\mathbb A$. Let $du$ be a finite measure on $\hat{\mathbb Z}^\times$, and let $\Phi : \mathbb A^3 \to \mathbb C$ be a product $\Phi(x) = \prod_{i<3} \Phi_i(x_i)$ of three functions each lying in [`NumberField.AdelicFourier.pureTensorSet ℚ`](def/NumberField_AdelicFourier.html#L75), i.e. of the form $x \mapsto f(x_\infty)h(x_{\mathrm{fin}})$ with $f$ Schwartz on the mixed space of $\mathbb Q$ and $h$ locally constant with compact support on the finite adeles. Then there are a real constant $C$ and a natural number $M$ such that for every $g \in \mathrm{GL}_3(\mathbb A)$ with `TateGlobal.ideleNorm ℚ (det g) = 1` there is a function $R : \mathbb R \to \mathbb C$ with, for all $\sigma \in (1,2]$,
--   $$\mathrm{epstein}\,du\,\Phi\,\sigma\,g \;=\; \frac{1}{\sigma-1}\cdot\frac{du(\hat{\mathbb Z}^\times)\int_{\mathbb A^3}\Phi\,dx}{3\,\mathrm{vol}(B^3)} \;+\; R(\sigma),$$
--   where the integral and the volume are taken for the product over the three coordinates of the additive Haar measure `adelicAddHaar` and $B =$ [`NumberField.AdelicBox.adelicBox ℚ`](def/NumberField_AdelicBox.html#L295) is the product of the fundamental parallelotope of the lattice basis at the infinite places with the integral finite adeles; and $\|R(\sigma)\| \le C\,(\mathrm{gauge3}\ \mathbb Q\ g)^M$ for all $\sigma \in (1,2]$. Here `epstein du Φ σ g` is $\mathrm{ideleNorm}(\det g)^\sigma \int_0^\infty t^{3\sigma}\int_{\hat{\mathbb Z}^\times} \sum_{0 \neq \xi \in \mathbb Q^3} \Phi(\mathrm{point}\ t\ u\ g\ \xi)\,du\,\frac{dt}{t}$, and $\mathrm{gauge3}$ is $\max\bigl(1, \mathrm{archGauge3}\cdot\mathrm{finGauge3}\bigr)$, the archimedean factor being $1$ plus the sum of the sizes of the components of $g$ at the infinite places and the finite factor the finprod of the sup-sizes of its local components.
--
--   This is the adelic Epstein zeta integral of a pure-tensor test function on $\mathrm{GL}_3$ over $\mathbb Q$, together with its Laurent expansion at $\sigma = 1$: a simple pole with residue proportional to $\int_{\mathbb A^3}\Phi$ and an error term bounded on $(1,2]$ uniformly in $g$ by a fixed power of the gauge, on the locus of norm-one determinant. It feeds [`LanglandsTunnell.CubicInduction.AdelicEpstein.integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor`](thm.html#LanglandsTunnell.CubicInduction.AdelicEpstein.integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor), where the residue is extracted after integration over the quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_exists_forall_epstein_eq_div_sub_one_add_of_pureTensor.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory

theorem
LanglandsTunnell.CubicInduction.AdelicEpstein.exists_forall_epstein_eq_div_sub_one_add_of_pureTensor
    [MeasurableSpace (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)]
    (hmeas : @Measurable (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) (AdeleRing (𝓞 ℚ) ℚ) _
      (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)
      (fun u => ((finUnitIdele u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)))
    (du : Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)) [IsFiniteMeasure du]
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (hΦ : ∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          Φ = fun x => ∏ i, Φc i (x i)) :
    ∃ (C : ℝ) (M : ℕ), ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) = 1 →
      ∃ R : ℝ → ℂ,
        (∀ σ ∈ Set.Ioc (1 : ℝ) 2,
          epstein du Φ σ g =
            (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
             (((du Set.univ).toReal : ℂ) *
                 (∫ x, Φ x ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) /
               (3 * (((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
                 (Set.univ.pi fun _ : Fin 3 => NumberField.AdelicBox.adelicBox ℚ)).toReal : ℂ))) /
             ((σ - 1 : ℝ) : ℂ) + R σ)) ∧
        (∀ σ ∈ Set.Ioc (1 : ℝ) 2, ‖R σ‖ ≤ C * gauge3 ℚ g ^ M) := by sorry
