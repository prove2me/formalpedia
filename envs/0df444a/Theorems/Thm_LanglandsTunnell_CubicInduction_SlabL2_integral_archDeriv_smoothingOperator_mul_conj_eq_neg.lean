-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_integral_archDeriv_smoothingOperator_mul_conj_eq_neg
-- name    : LanglandsTunnell.CubicInduction.SlabL2.integral_archDeriv_smoothingOperator_mul_conj_eq_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/cb4ecd42-7cfb-5b72-9e6e-8986a238009f
-- title:
--   Skew-adjointness of archimedean derivatives on the slab
-- statement:
--   Fix a homomorphism $\omega$ from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$ all of whose values have absolute value $1$, reals $a,b$ and a subset $\Phi_0$ of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ forming a slab domain, i.e. $0<a<b$ and $\Phi_0$ is a fundamental domain, for the image of $\mathrm{GL}_3(\mathbb{Q})$, of the adelic Haar measure on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ restricted to the region where the idelic norm of the determinant lies in the slab cut out by $a,b$. Assume a Siegel-type covering hypothesis: there are $c>0$ and $C$ such that every $g$ can be written, after left translation by some $\gamma\in\mathrm{GL}_3(\mathbb{Q})$, as $n t k$ where $n$ and $t$ are trivial at every finite place and $k$ lies in the local maximal compact subgroup (entries of $k$ and $k^{-1}$ of valuation $\le 1$) at every finite place, while at each infinite place $n$ is upper unipotent with entries bounded by $C$, $t$ is diagonal with both successive root values $\ge c$, and $k$ is orthogonal. Let $u$ be a continuous complex function on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, invariant under left translation by $\mathrm{GL}_3(\mathbb{Q})$, satisfying $u(z g)=\omega(z)u(g)$ for central ideles $z$, of moderate growth (bounded by a constant times a power of the gauge `gauge3`), and cuspidal along both maximal parabolics in the sense that the iterated integrals of $u(\mathrm{radicalP21}\,[x,y]\cdot g)$ and of $u(\mathrm{radicalP12}\,[x,y]\cdot g)$ vanish for all $g$, the adelic variables being integrated against additive Haar measure conditioned on the adelic box. Let $\varphi,\varphi'$ be smoothing kernels, i.e. each is the product of a smooth compactly supported archimedean factor in the real entries, supported away from vanishing determinant, with the indicator of a product of open compact subgroups agreeing with the local maximal compacts at cofinitely many finite places. Then for all $i,j\in\{0,1,2\}$, with $\partial_{ij}$ the derivative at $s=0$ of right translation by the lift of $1+sE_{ij}$ and $\varphi\ast u$ the smoothing $x\mapsto\int \varphi(g)u(xg)$, $$\int_{\Phi_0}\partial_{ij}(\varphi\ast u)(g)\,\overline{(\varphi'\ast u)(g)}\,dg=-\int_{\Phi_0}(\varphi\ast u)(g)\,\overline{\partial_{ij}(\varphi'\ast u)(g)}\,dg,$$ both integrals taken against the slab measure restricted to $\Phi_0$.
--
--   This is the skew-adjointness of the archimedean right-translation derivatives $\partial_{E_{ij}}$ for the $L^2$ pairing on the slab fundamental domain, applied to smoothed cuspidal functions on $\mathrm{GL}_3$ over $\mathbb{Q}$. It is used by [`LanglandsTunnell.CubicInduction.smoothingModule_slabForm`](thm.html#LanglandsTunnell.CubicInduction.smoothingModule_slabForm) in constructing the Lie-algebra action on the smoothed cuspidal space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_integral_archDeriv_smoothingOperator_mul_conj_eq_neg.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem LanglandsTunnell.CubicInduction.SlabL2.integral_archDeriv_smoothingOperator_mul_conj_eq_neg
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (hW0a :
      ∃ c C : ℝ, 0 < c ∧ ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ∃ (γ : GL (Fin 3) ℚ) (n t k : AdelicGL 3 (𝓞 ℚ) ℚ),
          globalPointsGL 3 (𝓞 ℚ) ℚ γ * g = n * t * k ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
          ∀ w : InfinitePlace ℚ,
            (∀ i j : Fin 3,
              (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
              (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
              ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
            (∀ i j : Fin 3, i ≠ j →
              (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
            (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
                (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1)
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous u)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (hmg : IsModerateGrowth3 ℚ u)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) u)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) u)
    (φ φ' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ) (hφ' : IsSmoothingKernel φ') (i j : Fin 3) :
    ∫ g, WhittakerBlock.archDeriv i j (smoothingOperator φ u) g * (starRingEnd ℂ) (smoothingOperator φ' u g)
        ∂(domainMeasure a b Φ₀) =
      - ∫ g, smoothingOperator φ u g * (starRingEnd ℂ) (WhittakerBlock.archDeriv i j (smoothingOperator φ' u) g)
        ∂(domainMeasure a b Φ₀) := by sorry
