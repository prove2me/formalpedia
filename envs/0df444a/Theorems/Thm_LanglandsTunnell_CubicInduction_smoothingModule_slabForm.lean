-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_smoothingModule_slabForm
-- name    : LanglandsTunnell.CubicInduction.smoothingModule_slabForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/a2131d68-abb0-5485-9a6f-37ca8820a9fd
-- title:
--   The slab form on the GL₃ smoothing module
-- statement:
--   Fix a homomorphism $\omega$ from the idele group of $\mathbb{Q}$ to $\mathbb{C}^{\times}$ with $|\omega(z)|=1$ for all $z$, and a continuous $f:\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ which is invariant under left translation by the rational points $\mathrm{GL}_3(\mathbb{Q})$, transforms by $\omega$ under left translation by central ideles, is slowly increasing for the gauge `gauge3` on all of the group, has vanishing integrals over the radicals `radicalP21` and `radicalP12` against the additive measure of the pins `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`, is smooth in the archimedean matrix entries on the invertible locus (`IsArchSmooth3`), and whose right translates $g\mapsto f(gk)$ by all $k$ that are trivial at every finite place and orthogonal at infinity lie in the span of one finite set of functions. Let $c:\mathrm{Fin}\,n\to\mathbb{C}$ and $t:\mathrm{Fin}\,n\to\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ with each $t_i$ trivial at infinity, and assume $x\mapsto\sum_i c_i f(xt_i)$ is `IsCentreFinite`, i.e. annihilated by monic polynomials in each of the three operators `casimir1`, `casimir2`, `casimir3` built from the archimedean derivatives. Let $u$ lie in the $\mathbb{C}$-span of the functions obtained by applying a word of operators `WhittakerBlock.archDeriv` $i$ $j$ to $g\mapsto\sum_i c_i f(ght_i)$, $h$ arbitrary. Further data: $m,J$, an injective $e:\mathrm{Fin}\,m\to\mathbb{C}$, coefficient functions $a_{ij}$ continuous on $\{y>0\}\times\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, an exponent $\tau>1/2$, and the hypothesis that for every compact $K$ and every $b\ge 1$ there is $C$ with $\bigl\|W_u(\mathrm{diag}(y_1y_2,y_2,1)k)-\sum_{i,j}a_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^j\bigr\|\le Cy_1^{\tau}$ for $k\in K$, $b^{-1}\le y_2\le b$ and $0<y_1\le 1$, where $W_u$ is `whittaker3` of $u$ for the above pins and the standard additive character `psiQ`; an index $i_0$ with $\mathrm{Re}\,e_{i_0}=1/2$; and a set $\Phi_0$ which is a fundamental domain for the image of $\mathrm{GL}_3(\mathbb{Q})$ with respect to the measure `slabMeasure 1 2`. Write $M$ for the $\mathbb{C}$-span of the functions `smoothingOperator` $\varphi$ $u$, i.e. $x\mapsto\int\varphi(g)u(xg)\,dg$, as $\varphi$ runs over the smoothing kernels (a smooth compactly supported archimedean factor supported where the matrix is invertible, times the indicator of a product of compact open subgroups agreeing with `localMaximalCompact3` at almost all places) whose left translates $g\mapsto\varphi(k^{-1}g)$, for $k$ trivial at the finite places and orthogonal at infinity, all lie in the span of a single finite set. Put $B(w,w')=\int w(g)\overline{w'(g)}\,d\mu$ with $\mu$ the slab measure `slabMeasure 1 2` restricted to $\Phi_0$. The conclusion is fourfold: $B(zw_1+w_2,w')=zB(w_1,w')+B(w_2,w')$ for all $z\in\mathbb{C}$ and $w_1,w_2,w'\in M$ (linearity is asserted in the first argument only); $\mathrm{Re}\,B(w,w)>0$ for every nonzero $w\in M$; $B(\mathrm{archDeriv}_{ij}w,w')=-B(w,\mathrm{archDeriv}_{ij}w')$ for all $w,w'\in M$ and $i,j\in\mathrm{Fin}\,3$; and $B(w(\cdot\,k),w'(\cdot\,k))=B(w,w')$ for all $w,w'\in M$ and all $k$ trivial at every finite place with orthogonal archimedean component.
--
--   This is the analytic side of the smoothing-module construction for $\mathrm{GL}_3$ over $\mathbb{Q}$: the smoothed translates of a centre-finite cuspidal vector carry a positive form, invariant under right translation by the maximal compact at infinity and skew for the Lie-algebra operators. It is used in the assembly of `exists_smoothingSubmodule_leadingCoeff_form_of_expCoeff_re_eq_one_half_centreFinite_mg`, where the form is combined with the leading-coefficient map attached to the exponent $e_{i_0}$ of real part $1/2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_smoothingModule_slabForm.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.smoothingModule_slabForm
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (hmg : IsModerateGrowth3 ℚ f)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite fun x => ∑ i, c i * f (x * t i))
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hu : u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
          φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
            (fun g => ∑ i, c i * f (g * h * t i)) w})
    (m J : ℕ) (e : Fin m → ℂ) (he : Function.Injective e)
    (a : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => a i j p.1 p.2) {p | 0 < p.1})
    (τ : ℝ) (hτ : 1 / 2 < τ)
    (hexp : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, a i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ)
    (i₀ : Fin m) (hD : (e i₀).re = 1 / 2)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain 1 2 Φ₀) :
    (∀ (z : ℂ), ∀ w₁ ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ w₂ ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ w' ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), (fun w w' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ => ∫ g, w g * (starRingEnd ℂ) (w' g) ∂(domainMeasure 1 2 Φ₀)) (z • w₁ + w₂) w' = z * (fun w w' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ => ∫ g, w g * (starRingEnd ℂ) (w' g) ∂(domainMeasure 1 2 Φ₀)) w₁ w' + (fun w w' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ => ∫ g, w g * (starRingEnd ℂ) (w' g) ∂(domainMeasure 1 2 Φ₀)) w₂ w') ∧
    (∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), w ≠ 0 → 0 < ((fun w w' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ => ∫ g, w g * (starRingEnd ℂ) (w' g) ∂(domainMeasure 1 2 Φ₀)) w w).re) ∧
    (∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ w' ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ i j : Fin 3,
          (fun w w' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ => ∫ g, w g * (starRingEnd ℂ) (w' g) ∂(domainMeasure 1 2 Φ₀)) (WhittakerBlock.archDeriv i j w) w' = - (fun w w' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ => ∫ g, w g * (starRingEnd ℂ) (w' g) ∂(domainMeasure 1 2 Φ₀)) w (WhittakerBlock.archDeriv i j w')) ∧
    ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ w' ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), (fun w w' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ => ∫ g, w g * (starRingEnd ℂ) (w' g) ∂(domainMeasure 1 2 Φ₀)) (fun g => w (g * k)) (fun g => w' (g * k)) = (fun w w' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ => ∫ g, w g * (starRingEnd ℂ) (w' g) ∂(domainMeasure 1 2 Φ₀)) w w' := by sorry
