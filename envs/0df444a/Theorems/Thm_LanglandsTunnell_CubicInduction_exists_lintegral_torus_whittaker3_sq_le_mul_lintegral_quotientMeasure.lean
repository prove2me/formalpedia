-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_lintegral_torus_whittaker3_sq_le_mul_lintegral_quotientMeasure
-- name    : LanglandsTunnell.CubicInduction.exists_lintegral_torus_whittaker3_sq_le_mul_lintegral_quotientMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/81a4b4ae-35d4-58b2-b72a-b82ad3171c7a
-- title:
--   Torus slices of squared Whittaker coefficients dominated on compacta
-- statement:
--   Fix a compact set $B \subseteq \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$. The assertion is the existence of a constant $C \in [0,\infty]$ with $C \neq \infty$ such that the following holds for every continuous $F \colon \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ that is left invariant under the image of $\mathrm{GL}_3(\mathbb{Q})$ under the entrywise map `globalPointsGL`, every measurable $\Phi \colon \mathbb{A}_{\mathbb{Q}}^3 \to \mathbb{C}$, and every $\sigma \in [1,2]$. Write $W(g) = \int\!\!\int\!\!\int F(u_3(x,y,z)\,g)\,\psi_{\mathbb{Q}}(-(x+y))$, the triple integral defining `whittaker3` taken against the measure attached to `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`, namely the adelic additive Haar measure conditioned on the adelic box, with $\psi_{\mathbb{Q}}$ the standard additive character `psiQ`. For $a \in (0,\infty)^3$ let $t(a) =$ [`WhittakerBlock.archRealLift3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18) applied to the diagonal real matrix with entries $a_0,a_1,a_2$. Then the lower Lebesgue integral over $k \in B$, against the Haar measure `adelicGLHaar` on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, of the integral over $a \in (0,\infty)^3$ against Lebesgue measure of $$\|W(t(a)k)\|^2\,\|\Phi(\text{row }2\text{ of } t(a)k)\|\,a_0^{\sigma-3}a_1^{\sigma-1}a_2^{\sigma+1}$$ is at most $C$ times the integral over the orbit quotient of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ by `unipotentSubgroup3`, against [`WhittakerBlock.quotientMeasure`](def/LanglandsTunnell_CubicInduction_WhittakerBlock.html#L28), of $\|W(q.\mathrm{out})\|^2\,\|\Phi(\text{row }2\text{ of } q.\mathrm{out})\|\,\mathrm{ideleNorm}_{\mathbb{Q}}(\det q.\mathrm{out})^{\sigma}$, all norms being taken in $\mathbb{R}_{\geq 0}$ and the products computed in $[0,\infty]$.
--
--   This is the domination step in the convergence analysis of the Rankin–Selberg type integral attached to a Whittaker coefficient on $\mathrm{GL}_3$ over $\mathbb{Q}$: the archimedean torus slices over a compact set of translates are bounded by a single integral over the unipotent quotient, the integrand of the latter being well defined on the quotient because the absolute value of the Whittaker coefficient is invariant under left translation by `unipotentSubgroup3`. It is used by [`LanglandsTunnell.CubicInduction.exists_lintegral_torus_whittaker3_sq_le_div_sub_one_of_isCuspidalAlong_of_isRightInvariant`](thm.html#LanglandsTunnell.CubicInduction.exists_lintegral_torus_whittaker3_sq_le_div_sub_one_of_isCuspidalAlong_of_isRightInvariant), where the bound is turned into a statement with explicit dependence on $\sigma - 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_lintegral_torus_whittaker3_sq_le_mul_lintegral_quotientMeasure.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem
LanglandsTunnell.CubicInduction.exists_lintegral_torus_whittaker3_sq_le_mul_lintegral_quotientMeasure
    (B : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hB : IsCompact B) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous F →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g) →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ, Measurable Φ →
        ∀ σ : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 →
        (letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
          ∫⁻ k in B, (∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)),
              (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                    NumberField.StandardAddChar.psiQ F
                    (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k)‖₊ : ℝ≥0∞) ^ 2 *
                (‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                    AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
                ENNReal.ofReal (a 0 ^ (σ - 3) * a 1 ^ (σ - 1) * a 2 ^ (σ + 1)) ∂volume)
            ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤
          C * ∫⁻ q,
            ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                    NumberField.StandardAddChar.psiQ F q.out‖₊ : ℝ≥0∞) ^ 2 *
              (‖Φ fun j : Fin 3 => (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det q.out) ^ σ))
            ∂WhittakerBlock.quotientMeasure) := by sorry
