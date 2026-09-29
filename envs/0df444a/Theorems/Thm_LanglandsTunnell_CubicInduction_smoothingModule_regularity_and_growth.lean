-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_smoothingModule_regularity_and_growth
-- name    : LanglandsTunnell.CubicInduction.smoothingModule_regularity_and_growth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/cf890db8-0f4e-5530-8267-58a19645156f
-- title:
--   Regularity and gauge growth in the GL₃ smoothing module
-- statement:
--   Let $\omega$ be a homomorphism from the idele group of $\mathbb{Q}$ to $\mathbb{C}^\times$ with $|\omega(z)|=1$ for all $z$, and let $f$ be a continuous function on $GL_3(\mathbb{A}_{\mathbb Q})$ that is invariant under left translation by the image of $GL_3(\mathbb{Q})$, satisfies $f(zg)=\omega(z)f(g)$ for adelic central scalars $z$, is of moderate growth ($\|f(g)\|\le C\,\mathrm{gauge3}(g)^N$ for some $C,N$), is cuspidal along both two-dimensional radicals `radicalP21` and `radicalP12` (the iterated integrals of $f$ over these radicals, against the adelic additive Haar measure conditioned to `AdelicBox.adelicBox`, vanish at every $g$), is archimedean-smooth (for each $g$ the map $e\mapsto f(g\cdot\mathrm{archRealLift3}\,e)$ is $C^\infty$ on the locus $\det e\neq 0$), and satisfies `hKf`: there is a finite set $s$ of functions such that $g\mapsto f(gk)$ lies in the $\mathbb{C}$-span of $s$ whenever $k$ is trivial at every finite place and has archimedean component in `orth3`. Let $c:\mathrm{Fin}\,n\to\mathbb{C}$ and $t:\mathrm{Fin}\,n\to GL_3(\mathbb{A})$ with all archimedean components trivial, and assume $x\mapsto\sum_i c_i f(x t_i)$ is centre-finite, i.e. each of `casimir1`, `casimir2`, `casimir3` satisfies a monic polynomial relation on it. Let $u$ lie in the $\mathbb{C}$-span of the functions obtained by applying a word of archimedean derivatives $\mathrm{archDeriv}\,i\,j$ (differentiation at $s=0$ of the right translate by $\mathrm{archRealLift3}(1+sE_{ij})$) to $g\mapsto\sum_i c_i f(ght_i)$, for words $w$ and elements $h$. Assume further expansion data: $m,J\in\mathbb{N}$, an injective $e:\mathrm{Fin}\,m\to\mathbb{C}$, functions $a_{ij}$ continuous on $\{y>0\}\times GL_3(\mathbb{A})$, a real $\tau>1/2$, and `hexp`: uniformly for $k$ in a compact set and $y_2$ in $[b^{-1},b]$, the Whittaker coefficient `whittaker3` of $u$ for the standard character $\psi_{\mathbb Q}$, evaluated at $\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2,y_2,1)\cdot k$, differs from $\sum_{i,j} a_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^j$ by at most $C y_1^{\tau}$ for $0<y_1\le 1$; and an index $i_0$ with $\mathrm{Re}\,e(i_0)=1/2$. Write $M$ for the $\mathbb{C}$-span of the functions $\mathrm{smoothingOperator}\,\varphi\,u$, where $\varphi$ runs over the smoothing kernels (of the form $\varphi(g)=\alpha(\mathrm{archEntries}\,g)$ times the indicator of $\{x:\ x_p\in K'_p\ \forall p\}$, with $\alpha$ smooth, compactly supported inside the locus of invertible matrices, and each $K'_p$ open and compact, equal to `localMaximalCompact3` for all but finitely many $p$) whose left translates $g\mapsto\varphi(k^{-1}g)$ by the $k$ described above all lie in the span of one finite set. The conclusion is twofold: first, every $w\in M$ is archimedean-smooth, its Whittaker coefficient `whittaker3` is archimedean-smooth, every archimedean derivative word applied to $w$ is continuous, and $w$ is invariant under left translation by $GL_3(\mathbb{Q})$; second, every $v\in M$ admits an $N\in\mathbb{N}$ such that for each derivative word there is a constant $C$ with $\|(\text{word applied to }v)(g)\|\le C\,\mathrm{gauge3}(g)^N$ for all $g$. The conclusion itself refers only to $u$ and to $M$, the expansion data entering through the surrounding hypotheses.
--
--   This is the regularity-and-growth half of the construction of the smoothing module attached to a cuspidal, centre-finite $GL_3$ seed vector: it records that smoothing a seed by an admissible kernel preserves automorphy, archimedean smoothness (also of the Whittaker coefficient), continuity of all derivative words, and uniform moderate growth of those words. It is used in the analysis of the leading coefficient of the Whittaker expansion at exponent of real part $1/2$, being cited by [`LanglandsTunnell.CubicInduction.exists_smoothingSubmodule_leadingCoeff_form_of_expCoeff_re_eq_one_half_centreFinite_mg`](thm.html#LanglandsTunnell.CubicInduction.exists_smoothingSubmodule_leadingCoeff_form_of_expCoeff_re_eq_one_half_centreFinite_mg), [`LanglandsTunnell.CubicInduction.smoothingModule_expansion_leadingCoeff`](thm.html#LanglandsTunnell.CubicInduction.smoothingModule_expansion_leadingCoeff) and [`LanglandsTunnell.CubicInduction.smoothingModule_orthFinite_and_archDeriv_mem`](thm.html#LanglandsTunnell.CubicInduction.smoothingModule_orthFinite_and_archDeriv_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_smoothingModule_regularity_and_growth.lean

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

theorem LanglandsTunnell.CubicInduction.smoothingModule_regularity_and_growth
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
    (i₀ : Fin m) (hD : (e i₀).re = 1 / 2) :
    (∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), WhittakerBlock.IsArchSmooth3 w ∧
        WhittakerBlock.IsArchSmooth3
          (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ w) ∧
        (∀ wd : List (Fin 3 × Fin 3),
          Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) w wd)) ∧
        ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), w (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = w g) ∧
    (∀ v ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∃ N : ℕ, ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) v w g‖ ≤ C * gauge3 ℚ g ^ N) := by sorry
