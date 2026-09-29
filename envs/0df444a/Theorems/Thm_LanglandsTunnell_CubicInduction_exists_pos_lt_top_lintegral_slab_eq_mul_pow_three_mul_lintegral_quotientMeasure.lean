-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_pos_lt_top_lintegral_slab_eq_mul_pow_three_mul_lintegral_quotientMeasure
-- name    : LanglandsTunnell.CubicInduction.exists_pos_lt_top_lintegral_slab_eq_mul_pow_three_mul_lintegral_quotientMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/8cd5421a-8b0e-5d58-883f-d869ff1252a2
-- title:
--   Unfolding a GL₃ Epstein integral to the Whittaker quotient
-- statement:
--   Let $\omega\colon (\mathbb{A}_{\mathbb{Q}})^{\times}\to\mathbb{C}^{\times}$ be a group homomorphism with $\|\omega(z)\|=1$ for all $z$, let $a,b\in\mathbb{R}$ and let $\Phi_0\subseteq\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ satisfy `IsSlabDomain a b Φ₀`, i.e. $0<a<b$ and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_3(\mathbb{Q})$ with respect to `slabMeasure a b`, the adelic Haar measure of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ restricted to the determinant slab `ideleNormDetSlab a b`. Let $du$ be a finite, non-zero measure on the group of unit ideles of $\mathbb{Q}$ (the units $\delta$ of the finite adele ring with $\delta$ and $\delta^{-1}$ integral at every finite place), measurable for the structure pulled back from the adele Borel structure. Then there is a constant $c$ with $0<c<\infty$ in $[0,\infty]$, depending only on these data, such that for every $F$ in `cuspFunctions ω a b Φ₀` — that is, $F\colon \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ invariant under left translation by $\mathrm{GL}_3(\mathbb{Q})$, satisfying $F(zg)=\omega(z)F(g)$ for central scalars $z$, lying in $L^2$ of `domainMeasure a b Φ₀` (the slab measure restricted to $\Phi_0$), continuous, and annihilated by the two radical integrals `IsCuspidalAlongP21` and `IsCuspidalAlongP12` taken against the adelic additive Haar measure conditioned on the adelic box $B=$ `AdelicBox.adelicBox ℚ` — for every measurable $\Phi\colon \mathbb{A}_{\mathbb{Q}}^3\to\mathbb{C}$ and every $\sigma\in\mathbb{R}$, $$\int^{-} \|F(g)\|^2\,\mathrm{epsteinPlus}\,du\,\Phi\,\sigma\,(g)\ d(\text{domainMeasure } a\,b\,\Phi_0) = c\cdot \mu(B)^3\cdot \int^{-}_{q} \|W_F(q.\mathrm{out})\|^2\,\|\Phi(e_3\, q.\mathrm{out})\|\, \| \det q.\mathrm{out}\|^{\sigma}\ d(\text{WhittakerBlock.quotientMeasure}),$$ where $\mathrm{epsteinPlus}$ is $\|\det g\|^{\sigma}$ times $\int_0^{\infty} t^{3\sigma}\int_{u}\sum_{0\neq\xi\in\mathbb{Q}^3}\|\Phi(\mathrm{point}\,t\,u\,g\,\xi)\|\,du\,\frac{dt}{t}$, $\mu$ is the adelic additive Haar measure, $W_F=$ `whittaker3` of $F$ for the pins `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) B` and the standard additive character `psiQ`, the integration variable $q$ runs over the quotient of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ by the orbit relation of the adelic upper unipotent subgroup `unipotentSubgroup3` with its Haar quotient measure, $e_3\,q.\mathrm{out}$ denotes the third row $j\mapsto (q.\mathrm{out})_{2j}$ of a chosen representative matrix, and the idele norm of the determinant is `TateGlobal.ideleNorm`. All integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions.
--
--   This is the Rankin–Selberg unfolding identity for $\mathrm{GL}_3$ over $\mathbb{Q}$: the $L^2$-pairing of a cusp function against a mirabolic Epstein–Eisenstein sum, integrated over a fundamental domain inside a determinant slab, is rewritten as an integral over the unipotent quotient in terms of the Whittaker coefficient of $F$, up to a positive finite constant and the cube of the Haar mass of the adelic box. It feeds the slab $L^2$ theory of the cubic induction, being used there in the construction and estimation of smoothing kernels and in the expansion of Whittaker coefficients under the smoothing operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_pos_lt_top_lintegral_slab_eq_mul_pow_three_mul_lintegral_quotientMeasure.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open NumberField LanglandsTunnell.CubicInduction.SlabL2
open LanglandsTunnell.CubicInduction
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
attribute [local instance] LanglandsTunnell.CubicInduction.AdelicEpstein.unitIdeleMeasurableSpace

theorem
LanglandsTunnell.CubicInduction.exists_pos_lt_top_lintegral_slab_eq_mul_pow_three_mul_lintegral_quotientMeasure
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (du : MeasureTheory.Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ))
    [MeasureTheory.IsFiniteMeasure du] [NeZero du] :
    ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
      ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, F ∈ cuspFunctions ω a b Φ₀ →
        ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ, Measurable Φ →
          ∀ σ : ℝ,
            ∫⁻ g, (‖F g‖₊ : ℝ≥0∞) ^ 2 * AdelicEpstein.epsteinPlus du Φ σ g ∂(domainMeasure a b Φ₀) =
            c * (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)) ^ 3 *
        (letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
          ∫⁻ q,
            ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                    NumberField.StandardAddChar.psiQ F q.out‖₊ : ℝ≥0∞) ^ 2 *
              (‖Φ fun j : Fin 3 => (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det q.out) ^ σ))
            ∂WhittakerBlock.quotientMeasure) := by sorry
