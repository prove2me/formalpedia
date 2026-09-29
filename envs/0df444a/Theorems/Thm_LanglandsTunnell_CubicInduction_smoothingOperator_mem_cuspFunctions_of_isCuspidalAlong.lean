-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong
-- name    : LanglandsTunnell.CubicInduction.smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/2381948b-ad92-5b02-b9dc-77bcd2322f3e
-- title:
--   Smoothing a cuspidal GL₃ function yields a slab cusp function
-- statement:
--   Fix a homomorphism $\omega \colon (\mathbb{A}_\mathbb{Q})^\times \to \mathbb{C}^\times$ of unit groups of the adele ring of $\mathbb{Q}$, real numbers $a, b$, and a set $\Phi_0 \subseteq GL_3(\mathbb{A}_\mathbb{Q})$ which is a slab domain for $a, b$, i.e. $0 < a < b$ and $\Phi_0$ is a fundamental domain for the left action of the image of $GL_3(\mathbb{Q})$ with respect to the measure `slabMeasure a b`. Assume a Siegel covering: there are $c > 0$ and $C$ such that every $g$ admits $\gamma \in GL_3(\mathbb{Q})$ and $n, t, k$ with $\gamma g = n t k$, where $n$ and $t$ have trivial component at every finite place and the component of $k$ at each finite place $p$ lies in `localMaximalCompact3`, the subgroup of matrices in $GL_3$ of the completion whose entries and whose inverse's entries all have valuation at most $1$; at each infinite place $w$ the component of $n$ has diagonal entries $1$, vanishing entries below the diagonal and all entries of norm at most $C$, the component of $t$ is diagonal with $c \le$ `archRoot₁` and $c \le$ `archRoot₂`, and the component $k_w$ satisfies $k_w^{\mathsf T} k_w = 1$. Let $f \colon GL_3(\mathbb{A}_\mathbb{Q}) \to \mathbb{C}$ be continuous, invariant under left multiplication by the image of $GL_3(\mathbb{Q})$, satisfying $f(zg) = \omega(z) f(g)$ for every idele $z$ viewed as a central scalar matrix, of moderate growth in the sense of `IsModerateGrowth3` (slow increase on all of $GL_3(\mathbb{A}_\mathbb{Q})$ relative to the gauge `gauge3`), and cuspidal along the two maximal parabolics in the sense that for every $g$ the double integral of $f(\mathrm{radicalP21}\,[x,y]\,g)$, respectively $f(\mathrm{radicalP12}\,[x,y]\,g)$, vanishes, the integrals being taken against the measure of the pin datum `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`, namely the additive adelic Haar measure conditioned on the adelic box $\{x : x_\infty \in \mathrm{infiniteBox}, \ x_{\mathrm{fin}} \text{ integral}\}$. Finally let $\varphi$ be a smoothing kernel: there are a smooth archimedean factor $\alpha$ on $3 \times 3$ real matrices and open compact subgroups $K'_p \le GL_3(\mathbb{Q}_p)$, equal to `localMaximalCompact3` for all but finitely many $p$, with $\varphi(g) = \alpha(\mathrm{archEntries}\,g)$ times the indicator of $\{x : x_p \in K'_p \text{ for all } p\}$. The conclusion is that the smoothed function $x \mapsto \int \varphi(g) f(xg)\,dg$, the integral against adelic Haar measure on $GL_3(\mathbb{A}_\mathbb{Q})$, belongs to `cuspFunctions ω a b Φ₀`: it lies in `automorphicSubmodule ω a b Φ₀`, is continuous, and is cuspidal along both parabolics for the same pin datum.
--
--   This is the statement that convolution with a smooth, compactly supported kernel carries a continuous cuspidal automorphic function of moderate growth on $GL_3$ over $\mathbb{Q}$ into the space of square-integrable cusp functions on a determinant-slab fundamental domain, the substance being the rapid decay of smooth cusp forms on Siegel sets. It feeds the quantitative bounds and orthogonality computations for the smoothing operator, and the construction of vanishing combinations of translates, used in the cubic induction step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2

theorem LanglandsTunnell.CubicInduction.smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (_hW0a :
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
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
    (_haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (_hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (_hmg : IsModerateGrowth3 ℚ f)
    (_hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (_hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hφ : IsSmoothingKernel φ) :
    smoothingOperator φ f ∈ cuspFunctions ω a b Φ₀ := by sorry
