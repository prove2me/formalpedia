-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_integral_smoothingOperator_comp_archRealLift3_mul_conj_eq
-- name    : LanglandsTunnell.CubicInduction.SlabL2.integral_smoothingOperator_comp_archRealLift3_mul_conj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/ef4c6c67-33e6-506a-aed3-b666e2658216
-- title:
--   Right archimedean translation preserves the slab L² pairing
-- statement:
--   Fix a character $\omega\colon (\mathbb{A}_{\mathbb{Q}}^{\times}) \to \mathbb{C}^{\times}$ of the ideles with $\lvert\omega(z)\rvert = 1$ for all $z$, reals $a,b$ and a set $\Phi_0$ of adelic points of $\mathrm{GL}_3$ which is a slab domain: $0 < a < b$ and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_3(\mathbb{Q})$ acting on the slab $\{a \le \lVert\det\rVert \le b\}$, equipped with the restriction `slabMeasure` of adelic Haar measure; `domainMeasure a b Φ₀` is the further restriction to $\Phi_0$. Assume the Siegel-type covering hypothesis `hW0a`: constants $c>0$ and $C$ such that every adelic $g$ admits $\gamma \in \mathrm{GL}_3(\mathbb{Q})$ and a factorisation $\gamma g = n t k$ in which $n$ and $t$ are trivial at every finite place, $k$ lies in the local maximal compact subgroup at every finite place, and at every infinite place $n$ is upper unipotent with all entries of norm $\le C$, $t$ is diagonal with both `archRoot₁` and `archRoot₂` at least $c$, and $k$ is orthogonal. Let $u$ be a continuous function on the adelic group, invariant under left multiplication by global points, satisfying $u(zg) = \omega(z)u(g)$ for central adelic scalars $z$, of moderate growth in the sense that $\lVert u(g)\rVert \le C' \,\mathrm{gauge}_3(g)^N$ for some $C', N$, and cuspidal along the two radicals $P_{21}$ and $P_{12}$: for every $g$ the double integral of $u(\mathrm{radical}(x,y)\,g)$ over the adele ring vanishes, the measure on the adeles being additive adelic Haar measure conditioned on the adelic box (infinite part in the fundamental domain of the lattice basis, finite part the integral adeles). Let $\varphi,\varphi'$ be smoothing kernels, i.e. each is the product of a smooth compactly supported archimedean factor whose support consists of invertible real matrices with the indicator of a family of open compact level subgroups at the finite places agreeing with the maximal compacts for almost all places, and let $e$ be a real $3 \times 3$ array with $\det e \neq 0$. Writing $(\varphi * u)(x) = \int \varphi(g)u(xg)$ against adelic Haar measure, and $L(e)$ for `archRealLift3 e` (the unit determined by the adelic matrix with archimedean entries $e$ and no finite contribution, and $1$ if that matrix is not invertible), the conclusion is
--   $$\int (\varphi * u)(gL(e))\,\overline{(\varphi' * u)(gL(e))}\,d\mu = \int (\varphi * u)(g)\,\overline{(\varphi' * u)(g)}\,d\mu,$$
--   where $\mu$ is `domainMeasure a b Φ₀`.
--
--   This is the invariance of the Petersson-type pairing on the slab fundamental domain under right translation by an archimedean element, in the polarised form needed for the pairing of two distinct smoothed cusp forms. It is used in the proof that the archimedean derivative of this pairing is antisymmetric.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_integral_smoothingOperator_comp_archRealLift3_mul_conj_eq.lean

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
open LanglandsTunnell.CubicInduction
open LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem LanglandsTunnell.CubicInduction.SlabL2.integral_smoothingOperator_comp_archRealLift3_mul_conj_eq
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
    (φ φ' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ) (hφ' : IsSmoothingKernel φ')
    (e : Fin 3 → Fin 3 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    ∫ g, smoothingOperator φ u (g * WhittakerBlock.archRealLift3 e) *
        (starRingEnd ℂ) (smoothingOperator φ' u (g * WhittakerBlock.archRealLift3 e)) ∂(domainMeasure a b Φ₀) =
      ∫ g, smoothingOperator φ u g * (starRingEnd ℂ) (smoothingOperator φ' u g) ∂(domainMeasure a b Φ₀) := by sorry
