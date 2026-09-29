-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq
-- name    : LanglandsTunnell.CubicInduction.exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/e63fdeb8-db45-51e2-b453-a924d0653788
-- title:
--   Non-orthogonal right translates of two cuspidal GL₃ forms
-- statement:
--   Fix a finite set $S$ of finite places of $\mathbb{Q}$, a homomorphism $\omega$ from the idele units of $\mathbb{Q}$ to $\mathbb{C}^\times$ with $\|\omega(z)\|=1$ for all $z$, functions $\lambda_1,\lambda_2$ on the finite places, reals $a,b$ and a set $\Phi_0\subseteq \mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ with `IsSlabDomain a b Φ₀`, i.e. $0<a<b$ and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_3(\mathbb{Q})$ with respect to Haar measure restricted to the idele-norm-determinant slab. Let `adm` be a predicate on functions $\varphi:\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ such that each `adm` function is continuous, left invariant under $\mathrm{GL}_3(\mathbb{Q})$, satisfies $\varphi(z g)=\omega(z)\varphi(g)$ for central adelic scalars $z$, and for each $p\notin S$ is right invariant under the image of `localMaximalCompact3` at $p$ and a coset eigenfunction there for $\mathrm{diag}(\varpi_p,1,1)$ and $\mathrm{diag}(\varpi_p,\varpi_p,1)$ with eigenvalues $\lambda_1(p),\lambda_2(p)$ (hypothesis `hadm`); and such that each `adm` function lies in `cuspFunctions ω a b Φ₀`, namely it is continuous, belongs to the automorphic submodule (left $\mathrm{GL}_3(\mathbb{Q})$-invariance, central transformation by $\omega$, and $L^2$ for the measure on $\Phi_0$ inside the slab), and is cuspidal along both $P_{21}$ and $P_{12}$ for the pins `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`. Let $V,L\in[0,\infty]$ with $L\neq 0,\infty$, and let $\ell$ assign to a function $\varphi$ and a function $\Phi$ on $\mathbb{A}_\mathbb{Q}^3$ a value in $[0,\infty]$. Call $\Phi$ a test function when it factors as $\Phi(x)=\prod_i\Phi_i(x_i)$ with each $\Phi_i$ a pure tensor that is factorisable and standard outside $S$, when $\Phi$ takes non-negative real values, and when $\int \mathrm{Re}\,\Phi>0$ for the product adelic Haar measure. Assume: $\ell(\varphi,\Phi)\neq\infty$ for `adm` $\varphi$ and test $\Phi$, with $\ell(\varphi,\Phi)\neq 0$ when $\varphi\neq 0$; for all $\varphi,\Phi$, $\ell(\varphi,\Phi)=\mathrm{ofReal}\big((\int\mathrm{Re}\,\Phi)/(3\,\mathrm{vol}(\mathrm{box}^3))\cdot\int\|\varphi\|^2\big)$ over the slab domain; and for `adm` $\varphi$ and test $\Phi$ the Whittaker block $\sigma\mapsto$ [`WhittakerBlock.block`](def/LanglandsTunnell_CubicInduction_WhittakerBlock.html#L40) of $\varphi$ against $\Phi$ for the standard additive character $\psi_\mathbb{Q}$ and the shell away from $S$ tends to its value at $\sigma=1$ as $\sigma\to 1^+$ within $(1,\infty)$, and that value times $V\cdot L$ equals $\ell(\varphi,\Phi)$. Finally let $f,f'$ be non-zero `adm` functions such that every finite linear combination $x\mapsto\sum_i c_i\,\varphi_i(x t_i)$ with each $\varphi_i\in\{f,f'\}$ and each $t_i$ having trivial component at every $p\notin S$ is again `adm`. Then there are $g,g'\in\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ with $x\mapsto f(xg)$ and $x\mapsto f'(xg')$ in the automorphic submodule whose images under `toL2` have non-zero inner product in $L^2$ of the slab domain.
--
--   This is the non-orthogonality step in the construction of the slab $L^2$ carrier for cuspidal forms on $\mathrm{GL}_3$ over $\mathbb{Q}$: from the proportionality of Whittaker blocks at exponent one to $L^2$ masses it produces right translates of two non-zero forms with non-vanishing pairing. It is used in the construction of smoothing kernels and of Whittaker expansions for the smoothing operator on the same carrier.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.CubicInduction.SlabL2
open scoped ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem
    LanglandsTunnell.CubicInduction.exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (adm : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → Prop)
    (hadm : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      Continuous φ ∧
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * φ g) ∧
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) φ) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen1 p)) φ (lam1 p)) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen2 p)) φ (lam2 p)))
    (hcusp : ∀ φ, adm φ → φ ∈ cuspFunctions ω a b Φ₀)
    (V L : ℝ≥0∞) (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (ℓ : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ((Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) → ℝ≥0∞)
    (hℓ : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
      ℓ φ Φ ≠ ⊤ ∧ (φ ≠ 0 → ℓ φ Φ ≠ 0))
    (hℓeq : ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ),
          ℓ φ Φ =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
          ENNReal.ofReal
            ((∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) /
                (3 * ((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
                  (Set.univ.pi fun _ : Fin 3 => NumberField.AdelicBox.adelicBox ℚ)).toReal) *
              ∫ g, ‖φ g‖ ^ 2 ∂(domainMeasure a b Φ₀))))
    (hF2 :
        ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
        ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
          (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
            (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
            Φ = fun x => ∏ i, Φc i (x i)) ∧
          (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
           0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        Filter.Tendsto
            (fun σ : ℝ => WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ φ Φ σ S)
            (nhdsWithin 1 (Set.Ioi 1))
            (nhds (WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ φ Φ 1 S)) ∧
          WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ φ Φ 1 S * (V * L) = ℓ φ Φ)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hf : adm f) (hf0 : f ≠ 0)
    (f' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hf' : adm f') (hf'0 : f' ≠ 0)
    (hmem :
        ∀ (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (φ : Fin n → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)),
          (∀ i, φ i = f ∨ φ i = f') →
          (∀ i, ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (t i) = 1) →
          adm (fun x => ∑ i, c i * φ i (x * t i))) :
    ∃ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f ∈ automorphicSubmodule ω a b Φ₀)
      (g' : AdelicGL 3 (𝓞 ℚ) ℚ) (hg' : translateRight g' f' ∈ automorphicSubmodule ω a b Φ₀),
      ⟪toL2 ω a b Φ₀ ⟨translateRight g f, hg⟩, toL2 ω a b Φ₀ ⟨translateRight g' f', hg'⟩⟫_ℂ ≠ 0 := by sorry
