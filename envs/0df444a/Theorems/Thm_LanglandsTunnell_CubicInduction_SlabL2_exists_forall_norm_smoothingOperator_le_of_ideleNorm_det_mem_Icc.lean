-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_forall_norm_smoothingOperator_le_of_ideleNorm_det_mem_Icc
-- name    : LanglandsTunnell.CubicInduction.SlabL2.exists_forall_norm_smoothingOperator_le_of_ideleNorm_det_mem_Icc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/6dfe72a5-5612-595b-a3c2-461141098168
-- title:
--   Smoothed GL₃ cusp forms are bounded on determinant slabs
-- statement:
--   Fix a character $\omega$ of the idele units of $\mathbb{Q}$ with values in $\mathbb{C}^\times$. The hypothesis `hW0a` is a Siegel covering assumption: there are reals $c>0$ and $C$ such that every $g\in GL_3(\mathbb{A}_\mathbb{Q})$ admits $\gamma\in GL_3(\mathbb{Q})$ and $n,t,k\in GL_3(\mathbb{A}_\mathbb{Q})$ with $\gamma g=ntk$, where $n$ and $t$ have trivial component at every finite place $p$, the component of $k$ at each $p$ lies in `localMaximalCompact3` (all entries of it and of its inverse have valuation at most $1$), and at each infinite place $w$: the $w$-component of $n$ has diagonal entries $1$, vanishing entries below the diagonal and all entries of norm at most $C$, the $w$-component of $t$ is diagonal with $c \le$ `archRoot₁ ℚ w t` and $c \le$ `archRoot₂ ℚ w t`, and the $w$-component of $k$ is orthogonal. Let $u:GL_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ be continuous, invariant under left translation by rational points, satisfying $u(zg)=\omega(z)u(g)$ for central ideles $z$, slowly increasing on all of $GL_3(\mathbb{A}_\mathbb{Q})$ with respect to `gauge3 ℚ`, and cuspidal along both $P_{21}$ and $P_{12}$ in the sense that for every $g$ the iterated integral of $u(\mathrm{radical}(x,y)\,g)$ over two copies of additive adelic Haar measure conditioned on the adelic box vanishes. Let $\varphi$ be a smoothing kernel, i.e. $\varphi(g)=\alpha(\text{archimedean entries of }g)$ times the indicator of those $g$ whose component at each $p$ lies in $K'_p$, for some smooth archimedean factor $\alpha$ and compact open subgroups $K'_p\le GL_3(\mathbb{Q}_p)$ agreeing with `localMaximalCompact3` for all but finitely many $p$. Then for all reals $0<a'<b'$ there is $B$ such that $\bigl\lVert\int \varphi(y)\,u(gy)\,dy\bigr\rVert\le B$, the integral being over adelic Haar measure on $GL_3(\mathbb{A}_\mathbb{Q})$, for every $g$ whose determinant has idele norm (the distributive Haar character of the adele ring) in $[a',b']$.
--
--   This is the boundedness — rapid decay with exponent zero — of a smoothed cusp form on $GL_3(\mathbb{A}_\mathbb{Q})$, restricted to a slab where the idele norm of the determinant is bounded above and below. It is used in the analytic input to the cubic induction, where such bounds make the inner products of smoothed cusp forms against archimedean translates differentiable.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_forall_norm_smoothingOperator_le_of_ideleNorm_det_mem_Icc.lean

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

theorem LanglandsTunnell.CubicInduction.SlabL2.exists_forall_norm_smoothingOperator_le_of_ideleNorm_det_mem_Icc
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
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
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ)
    (a' b' : ℝ) (ha' : 0 < a') (hab' : a' < b') :
    ∃ B : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a' b' →
        ‖smoothingOperator φ u g‖ ≤ B := by sorry
