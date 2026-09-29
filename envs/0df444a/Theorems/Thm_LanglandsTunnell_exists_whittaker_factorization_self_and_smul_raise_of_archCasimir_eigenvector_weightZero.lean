-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_whittaker_factorization_self_and_smul_raise_of_archCasimir_eigenvector_weightZero
-- name    : LanglandsTunnell.exists_whittaker_factorization_self_and_smul_raise_of_archCasimir_eigenvector_weightZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/aa97a870-4e49-503b-a9b4-cd6d201ba5f7
-- title:
--   Whittaker factorisation for a weight-zero cusp form and its raising
-- statement:
--   Work over $\mathbb{Q}$ with the production pins attached to the set $D=\bigcup_{x\in T}(\,\cdot\,x)[\,\mathrm{CS}(c,u,d_1,d_2)]$, a finite union of right translates of a centre-cut Siegel set, to the level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, to the Hecke elements $v\mapsto \mathrm{heckeGen}(v)$ and to the box `adelicBox`; here $d_1<d_2$ and $D$ meets every orbit of $\mathrm{GL}_2(\mathbb{Q})\backslash\mathrm{GL}_2(\mathbb{A})/Z$. Let $\Phi$ be a Hecke eigensystem with complex coefficients, $\psi$ a continuous nontrivial additive character of the adeles trivial on $\mathbb{Q}$ whose component at a real place $w$ is $x\mapsto e^{2\pi i x}$ (all other infinite components being killed), $\xi$ a character of the unit group of the adeles, $S$ a finite set of finite places, and $\varphi_1$ a nonzero complex-valued function on $\mathrm{GL}_2(\mathbb{A})$ which is an isotypic cusp form for these pins with central character $\xi$, level $\Phi.\mathrm{level}$, exceptional set $S$ and eigensystem $\Phi$, is reproduced by right convolution with some factorizable test function, is archimedean-smooth at $w$, satisfies $\mathrm{archCasimirAt}\,\varphi_1=(\tfrac14-((u_1-u_2)/2)^2)\varphi_1$ for complex $u_1,u_2$, has archimedean weight-zero character at every real place, and satisfies $\varphi_1(g\,J_w)=(-1)^{a}\varphi_1(g)$ for $a\in\mathbb{Z}/2$; assume moreover that the local component at $w$ of $\xi$ (transported along the top-subgroup identification) is $x\mapsto \|x\|^{\,\mathrm{mult}(w)(u_1+u_2+1)}(x/\|x\|)^{a_c}$ for some integer $a_c$. Put $\varphi_2=-(4\pi)^{-1}\bigl(D_H\varphi_1+i(D_E\varphi_1+D_{F^-}\varphi_1)\bigr)$, with $D_H,D_E,D_{F^-}$ the archimedean derivatives at $w$. Then there are a function $C$ of a finite adele and a group element and two functions $F_0,F_2:\mathbb{C}\to\mathbb{C}$ such that: for every idele unit $a'$ and every $g$ with trivial archimedean component, the first $\psi$-Whittaker coefficient of $\varphi_1$ at $\mathrm{diag}(a',1)g$ equals $\bigl(\prod_{w'}F_0(\iota_{w'}(a'_\infty(w')))\bigr)\,C(a'_{\mathrm{fin}},g)$, and that of $\varphi_2$ equals $\bigl(\prod_{w'}F_2(\iota_{w'}(a'_\infty(w')))\bigr)\,C(a'_{\mathrm{fin}},g)$ with the same $C$, the products running over all infinite places and $\iota_{w'}$ being the embedding of the completion into $\mathbb{C}$; $\varphi_2$ is again an isotypic cusp form for the same data, is nonzero, is reproduced by right convolution with a factorizable test function, and has archimedean weight-two character at every real place; $F_0(-t)=(-1)^{a}F_0(t)$ for all real $t$; and for $\mathrm{Re}\,s>\max(-\mathrm{Re}\,u_1,-\mathrm{Re}\,u_2)$ the Mellin integrals of $t\mapsto (F_0(t)+(-1)^{a}F_0(-t))/t$, of $t\mapsto (F_2(t)+(-1)^{a}F_2(-t))/t$ and of $t\mapsto (F_2(t)+(-1)^{a+1}F_2(-t))/t$ converge at $s$ and equal, respectively, the archimedean factor of the principal parameter $(u_1,a;u_2,a)$ twisted by $(0,a)$, that factor multiplied by $(2s+u_1+u_2-1)/(4\pi)$, and the archimedean factor of the same parameter twisted by $(0,a+1)$.
--
--   This is the archimedean multiplicity-one statement for $\mathrm{GL}_2$ over $\mathbb{Q}$ in adelic form: the first Whittaker coefficient of a weight-zero cusp vector with principal-series Casimir eigenvalue factors as an archimedean profile times a single function of the finite data, the same finite function serves the weight-two vector obtained by raising, and the symmetrised Mellin transforms of the two profiles are the expected products of Gamma factors. It feeds the corresponding statement for a cusp form of minimal weight, which is used to match the archimedean factor of an automorphic $L$-function with that of the analytic datum in the converse-theorem input to Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_whittaker_factorization_self_and_smul_raise_of_archCasimir_eigenvector_weightZero.lean

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

theorem LanglandsTunnell.exists_whittaker_factorization_self_and_smul_raise_of_archCasimir_eigenvector_weightZero
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ φ₁)
    (hne : φ₁ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁)
    (hsm : IsArchSmoothAt hw φ₁) (u₁ u₂ : ℂ) (a : ZMod 2)
    (hΩ : archCasimirAt hw φ₁ = (1 / 4 - ((u₁ - u₂) / 2) ^ 2) • φ₁)
    (hwt : ∀ (w' : InfinitePlace ℚ) (hw' : w'.IsReal), HasArchCharacterAt₀ ℚ w' (archWeightCharAt hw' 0) φ₁)
    (ac : ℤ) (hcen : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w (u₁ + u₂ + 1) ac)
    (hJ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ₁ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a.val * φ₁ g) :
    ∃ (C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (F₀ F₂ : ℂ → ℂ),

      (∀ a' : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
        whittakerCoefficient ℚ
            (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
            ψ φ₁ 1 (diagOne a' * g)
          = (∏ w' : InfinitePlace ℚ, F₀ (extensionEmbedding w' ((a' : AdeleRing (𝓞 ℚ) ℚ).1 w')))
              * C (a' : AdeleRing (𝓞 ℚ) ℚ).2 g) ∧
      (∀ a' : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
        whittakerCoefficient ℚ
            (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
            ψ ((-(1 / (4 * (Real.pi : ℂ)))) • (archDerivAt hw ArchDir.H φ₁
              + Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁))) 1 (diagOne a' * g)
          = (∏ w' : InfinitePlace ℚ, F₂ (extensionEmbedding w' ((a' : AdeleRing (𝓞 ℚ) ℚ).1 w')))
              * C (a' : AdeleRing (𝓞 ℚ) ℚ).2 g) ∧

      IsIsotypicCuspFormAt ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ξ Φ.level S Φ
          ((-(1 / (4 * (Real.pi : ℂ)))) • (archDerivAt hw ArchDir.H φ₁
              + Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁))) ∧
      ((-(1 / (4 * (Real.pi : ℂ)))) • (archDerivAt hw ArchDir.H φ₁
              + Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁))) ≠ 0 ∧
      (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧
        rightConv ℚ ((-(1 / (4 * (Real.pi : ℂ)))) • (archDerivAt hw ArchDir.H φ₁
              + Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁))) α
          = ((-(1 / (4 * (Real.pi : ℂ)))) • (archDerivAt hw ArchDir.H φ₁
              + Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁)))) ∧
      (∀ (w' : InfinitePlace ℚ) (hw' : w'.IsReal), HasArchCharacterAt₀ ℚ w' (archWeightCharAt hw' 2)
          ((-(1 / (4 * (Real.pi : ℂ)))) • (archDerivAt hw ArchDir.H φ₁
              + Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁)))) ∧

      (∀ t : ℝ, F₀ (-t) = (-1 : ℂ) ^ a.val * F₀ t) ∧

      (∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (F₀ t + (-1 : ℂ) ^ a.val * F₀ (-t)) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (F₀ t + (-1 : ℂ) ^ a.val * F₀ (-t)) / (t : ℂ)) s
            = ((RealArchParam.principal u₁ a u₂ a).twist 0 a).archFactor s) ∧
      (∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (F₂ t + (-1 : ℂ) ^ a.val * F₂ (-t)) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (F₂ t + (-1 : ℂ) ^ a.val * F₂ (-t)) / (t : ℂ)) s
            = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                * ((RealArchParam.principal u₁ a u₂ a).twist 0 a).archFactor s) ∧
      (∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (F₂ t + (-1 : ℂ) ^ (a + 1).val * F₂ (-t)) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (F₂ t + (-1 : ℂ) ^ (a + 1).val * F₂ (-t)) / (t : ℂ)) s
            = ((RealArchParam.principal u₁ a u₂ a).twist 0 (a + 1)).archFactor s) := by sorry
