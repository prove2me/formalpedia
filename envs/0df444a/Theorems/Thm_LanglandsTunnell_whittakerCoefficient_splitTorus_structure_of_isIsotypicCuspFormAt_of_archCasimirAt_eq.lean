-- Prove2me | Theorems.Thm_LanglandsTunnell_whittakerCoefficient_splitTorus_structure_of_isIsotypicCuspFormAt_of_archCasimirAt_eq
-- name    : LanglandsTunnell.whittakerCoefficient_splitTorus_structure_of_isIsotypicCuspFormAt_of_archCasimirAt_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/8a609727-a362-5739-9c60-28513503be94
-- title:
--   Torus structure of the first Whittaker coefficient over ℚ
-- statement:
--   Fix reals $c,u,d_1<d_2$ and a finite set $T\subset \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, and let $D=\bigcup_{x\in T}Dx$ with $D$ the centre-cut Siegel set of parameters $c,u,d_1,d_2$; assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ modulo rational points and the adelic centre. Let $\psi$ be a continuous nontrivial additive character of $\mathbb{A}_\mathbb{Q}$ trivial on $\mathbb{Q}$, let $w$ be a real place, and assume $\psi(x,0)=\exp(2\pi i\,x_w)$ for infinite adeles $x$ supported at $w$. Work with the pins $\mathrm{productionPinsOf}$ for $D$, the levels $\mathrm{levelOne}\,N\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators $\mathrm{heckeGen}$ and the adelic box; let $\xi$ be a character of the (full) unit group of its $Z$, $N$ an ideal, $S$ a finite set of finite places, $\Phi$ a Hecke eigensystem over $\mathbb{C}$, and $\varphi$ a nonzero function on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ that is an isotypic cusp form for these data, reproduced by right convolution with some factorizable test function, smooth at $w$, satisfying $\mathrm{archCasimirAt}\,\varphi=(\tfrac14-\nu^2)\varphi$, and of weight $k(w')$ at every real place $w'$ in the sense of $\mathrm{HasArchCharacterAt}_0$ for $\mathrm{archWeightCharAt}$. Assume the local component of $\xi$ at $w$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,u_c}(\iota_w(x)/\|x\|)^{a_c}$. Put $W=\mathrm{whittakerCoefficient}$ of $\varphi$ against $\psi$ at $\alpha=1$, i.e. $W(g)=\int\varphi(n(x)g)\psi(-x)\,dx$ for the conditioned adelic Haar measure on the box. The conclusion has five parts. First, $W$ is smooth at $w$, satisfies the same Casimir equation with eigenvalue $\tfrac14-\nu^2$, has weight $k(w)$ at $w$, and $W(n(x)_w p)=e^{2\pi i x}W(p)$ for all real $x$ and all $p$. Second (peeling of the centre), for every $g$, every $y>0$ and every unit $r$ of $\mathbb{Q}_w$ equal to $y$ (respectively $-y$) under the identification of $\mathbb{Q}_w$ with $\mathbb{R}$, $W(\mathrm{diag}(r,1)g)=(\sqrt y)^{u_c}\,W(T(\tfrac12\log y)_w g)$, respectively $(\sqrt y)^{u_c}\,W((J\,T(\tfrac12\log y))_w g)$, where $T(t)=\mathrm{diag}(e^t,e^{-t})$ and $J$ is the matrix of `UpperHalfPlane.J`. Third, for every $g$ with trivial archimedean component, the two sheet functions $y\mapsto W(T(\tfrac12\log y)_w g)$ and $y\mapsto W((J\,T(\tfrac12\log y))_w g)$ are differentiable on $(0,\infty)$, as are their first derivatives, and each satisfies the Whittaker equation $y^2 f''(y)+(\tfrac14-\nu^2+2\pi \kappa y-4\pi^2y^2)f(y)=0$ for $y>0$, with $\kappa=k(w)$ on the first sheet and $\kappa=-k(w)$ on the second. Fourth, for such $g$ each sheet function has moderate growth: there are $C',N'$ with $\|f(z)\|\le C'z^{N'}$ for $z\ge 1$. Fifth, a rank-one statement: if some $t_0$ with trivial archimedean component and some $y_0>0$ with corresponding unit $r_0$ satisfy $W(\mathrm{diag}(r_0,1)t_0)\ne 0$, then for every $h$ with trivial archimedean component, every $y>0$ and every unit $r$ corresponding to $y$, $W(\mathrm{diag}(r,1)h)=\dfrac{W(\mathrm{diag}(r_0,1)h)}{W(\mathrm{diag}(r_0,1)t_0)}\,W(\mathrm{diag}(r,1)t_0)$.
--
--   This is the archimedean analysis of the first Whittaker coefficient of a cusp form on $\mathrm{GL}_2$ over $\mathbb{Q}$: equivariance under the unipotent and central directions, the classical Whittaker differential equation on the two sheets of the real split torus, moderate growth, and the resulting factorisation of the coefficient into a product of a function of the finite variable and a function of the torus variable. It feeds the construction of Whittaker factorisations used in the converse-theorem step towards the Langlands–Tunnell theorem, in particular the statements on Casimir eigenvectors of minimal weight and of weight zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_whittakerCoefficient_splitTorus_structure_of_isIsotypicCuspFormAt_of_archCasimirAt_eq.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

theorem LanglandsTunnell.whittakerCoefficient_splitTorus_structure_of_isIsotypicCuspFormAt_of_archCasimirAt_eq
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) (w : InfinitePlace ℚ) (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Φ φ)
    (hne : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (ν : ℂ) (hΩ : archCasimirAt hw φ = (1 / 4 - ν ^ 2) • φ)
    (k : InfinitePlace ℚ → ℤ)
    (hwt : ∀ (w' : InfinitePlace ℚ) (hw' : w'.IsReal), HasArchCharacterAt₀ ℚ w' (archWeightCharAt hw' (k w')) φ)
    (uc : ℂ) (ac : ℤ) (hcen : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w uc ac)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW : W = whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1) :

    (IsArchSmoothAt hw W ∧ archCasimirAt hw W = (1 / 4 - ν ^ 2) • W ∧
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) W ∧
      ∀ (x : ℝ) (p : AdelicGL2 (𝓞 ℚ) ℚ),
        W (archRealGLAt hw (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p) ∧

    (∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (y : ℝ), 0 < y → ∀ r : (w.Completion)ˣ,
      ((r : w.Completion) = (ringEquivRealOfIsReal hw).symm y →
        W (diagOne (archUnitHom w r) * g)
          = ((Real.sqrt y : ℝ) : ℂ) ^ uc * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)) ∧
      ((r : w.Completion) = (ringEquivRealOfIsReal hw).symm (-y) →
        W (diagOne (archUnitHom w r) * g)
          = ((Real.sqrt y : ℝ) : ℂ) ^ uc
              * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g))) ∧

    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
      (DifferentiableOn ℝ (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
        DifferentiableOn ℝ (deriv (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)))
          (Set.Ioi 0) ∧
        ∀ y : ℝ, 0 < y →
          (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g))) y
              + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((k w : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2)
                * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g) = 0) ∧
      (DifferentiableOn ℝ
          (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
        DifferentiableOn ℝ
          (deriv (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)))
          (Set.Ioi 0) ∧
        ∀ y : ℝ, 0 < y →
          (y : ℂ) ^ 2 * deriv (deriv
                (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g))) y
              + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * (((-k w : ℤ) : ℝ) : ℂ) * (y : ℂ)
                  - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2)
                * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g) = 0)) ∧

    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
      (∃ C' N' : ℝ, ∀ z : ℝ, 1 ≤ z →
        ‖W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)‖ ≤ C' * z ^ N') ∧
      (∃ C' N' : ℝ, ∀ z : ℝ, 1 ≤ z →
        ‖W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)‖ ≤ C' * z ^ N')) ∧

    (∀ t₀ : AdelicGL2 (𝓞 ℚ) ℚ, t₀ ∈ finiteAdelicGL2Subgroup ℚ → ∀ y₀ : ℝ, 0 < y₀ → ∀ r₀ : (w.Completion)ˣ,
      (r₀ : w.Completion) = (ringEquivRealOfIsReal hw).symm y₀ → W (diagOne (archUnitHom w r₀) * t₀) ≠ 0 →
        ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ y : ℝ, 0 < y → ∀ r : (w.Completion)ˣ,
          (r : w.Completion) = (ringEquivRealOfIsReal hw).symm y →
            W (diagOne (archUnitHom w r) * h)
              = W (diagOne (archUnitHom w r₀) * h) / W (diagOne (archUnitHom w r₀) * t₀)
                  * W (diagOne (archUnitHom w r) * t₀)) := by sorry
