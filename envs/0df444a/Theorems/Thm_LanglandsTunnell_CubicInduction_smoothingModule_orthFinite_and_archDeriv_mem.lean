-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_smoothingModule_orthFinite_and_archDeriv_mem
-- name    : LanglandsTunnell.CubicInduction.smoothingModule_orthFinite_and_archDeriv_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/8e18c967-7398-51e5-a051-91e0150c6860
-- title:
--   Orthogonal finiteness and derivative stability of the smoothing module
-- statement:
--   Fix a character $\omega$ of the idèle units of $\mathbb{Q}$ with values in $\mathbb{C}^\times$ all of whose values have modulus $1$, and a continuous $f : \mathrm{GL}_3(\mathbb{A}_\mathbb{Q}) \to \mathbb{C}$ that is left invariant under the rational points `globalPointsGL`, satisfies $f(z g) = \omega(z) f(g)$ for adelic central scalars $z$, is of moderate growth (slowly increasing on all of $\mathrm{GL}_3(\mathbb{A})$ with respect to `gauge3`), has vanishing integrals over the two two-dimensional unipotent radicals `radicalP21` and `radicalP12` against the conditional adelic Haar measure attached to the adelic box, is archimedean-smooth in the sense that $e \mapsto f(g \cdot \mathrm{archRealLift3}\,e)$ is $C^\infty$ on the invertible real $3\times 3$ matrices for every $g$, and is orthogonally finite on the right: some finite set $s$ of functions spans, over $\mathbb{C}$, all translates $g \mapsto f(gk)$ with $k$ trivial at every finite place and archimedean component in `orth3` (i.e. $k^{\mathsf T}k = 1$). Fix further $n$, scalars $c : \mathrm{Fin}\,n \to \mathbb{C}$ and translates $t_i$ with trivial archimedean component such that $x \mapsto \sum_i c_i f(x t_i)$ is centre-finite, each of `casimir1`, `casimir2`, `casimir3` satisfying a monic polynomial relation on it; and $u$ in the $\mathbb{C}$-span of the functions obtained by applying words in the nine operators `WhittakerBlock.archDeriv i j` to the translates $g \mapsto \sum_i c_i f(ght_i)$, $h$ arbitrary. Fix finally expansion data: $m, J$, an injective $e : \mathrm{Fin}\,m \to \mathbb{C}$, coefficient functions $a_{ij}(y,g)$ jointly continuous on $\{y > 0\}$, an exponent $\tau > 1/2$, the hypothesis that on every compact set of $k$'s and every slab $b^{-1} \le y_2 \le b$ the Whittaker integral `whittaker3` of $u$ against the standard additive character $\psi_\mathbb{Q}$, evaluated at $\mathrm{diag}(y_1y_2, y_2, 1)k$, differs from $\sum_{i,j} a_{ij}(y_2,k)\, y_1^{e_i}(\log y_1)^j$ by $O(y_1^\tau)$ for $0 < y_1 \le 1$, and an index $i_0$ with $\mathrm{Re}\,e_{i_0} = 1/2$. Let $M$ be the $\mathbb{C}$-span of the functions $\mathrm{smoothingOperator}(\varphi, u) : x \mapsto \int \varphi(g) u(xg)\,dg$ (adelic Haar measure on $\mathrm{GL}_3$), where $\varphi$ runs over the admissible kernels: $\varphi$ is a smoothing kernel (a smooth compactly supported archimedean factor supported on matrices of nonzero determinant, times the indicator of a product of compact open subgroups equal to the standard maximal compact at almost all finite places) which in addition is orthogonally finite on the left, some finite set $S$ spanning all $g \mapsto \varphi(k^{-1}g)$ for $k$ trivial at the finite places with archimedean component in `orth3`. The conclusion is twofold: every $w \in M$ is orthogonally finite on the right in the same sense as $f$ above; and $M$ is stable under each of the nine derivatives `WhittakerBlock.archDeriv i j`.
--
--   This is the assembly step showing that the module of right smoothings of the chosen $\mathrm{GL}_3$ vector $u$ by admissible kernels is $K$-finite for the orthogonal group at infinity and closed under the nine right invariant derivatives at the archimedean place, so that it may serve as the ambient space for the slab inner product and the leading-coefficient functional. It is used in the constructions of the slab form, of the expansion leading coefficient, and in the existence statement for a smoothing submodule with leading-coefficient form at exponent of real part $1/2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_smoothingModule_orthFinite_and_archDeriv_mem.lean

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

theorem LanglandsTunnell.CubicInduction.smoothingModule_orthFinite_and_archDeriv_mem
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
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
    (∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))})) := by sorry
