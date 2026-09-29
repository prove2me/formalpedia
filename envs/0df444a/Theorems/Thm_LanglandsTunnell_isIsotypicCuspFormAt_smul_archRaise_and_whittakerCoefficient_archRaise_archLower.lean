-- Prove2me | Theorems.Thm_LanglandsTunnell_isIsotypicCuspFormAt_smul_archRaise_and_whittakerCoefficient_archRaise_archLower
-- name    : LanglandsTunnell.isIsotypicCuspFormAt_smul_archRaise_and_whittakerCoefficient_archRaise_archLower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/5c3280e2-587b-5192-bc05-ecedf19f73d3
-- title:
--   Raising operator: isotypy, weight k+2, Whittaker coefficients
-- statement:
--   Fix reals $c,u,d_1,d_2$ with $d_1<d_2$ and a finite set $T\subset \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ such that $D=\bigcup_{x\in T}(\cdot\,x)''\,\mathrm{centreCutSiegelSet}\,c\,u\,d_1\,d_2$ covers $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ modulo rational points on the left and central ideles on the right (`CoversModCentre`). Throughout, the carrier data are `productionPinsOf` for this $D$, with level subgroups $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}\,v$, full central group $Z=\top$ and the adelic Haar measure conditioned to `adelicBox`. Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex eigenvalues, $\psi$ a continuous nontrivial additive character of $\mathbb{A}_{\mathbb{Q}}$ trivial on $\mathbb{Q}$, $w$ a real place of $\mathbb{Q}$, $\xi:Z\to\mathbb{C}^{\times}$, $S$ a finite set of finite places, and $\varphi:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$. Assume: $\varphi$ is an isotypic cusp form for these data, i.e. a smooth cuspidal automorphic function with central character $\xi$, continuous, invariant under right translation by $U(\Phi.\mathrm{level})$, a Hecke coset eigenfunction with eigenvalue $\Phi.a\,v$ for every $v\notin S$ and satisfying $\varphi(\mathrm{scalar}(\det \mathrm{heckeGen}\,v)\,g)=(\mathrm{cNorm}\,v)^{-1}\Phi.b\,v\cdot\varphi(g)$ for $v\notin S$; $\varphi\neq 0$; $\varphi=\varphi*\alpha$ (right convolution) for some factorizable test function $\alpha$; $\varphi$ is smooth at $w$ in the sense of `IsArchSmoothAt`; and, for a function $k$ on infinite places, $\varphi$ satisfies `HasArchCharacterAt₀` at every real place $w'$ for the character $\mathrm{archWeightCharAt}\,hw'\,(k\,w')$, the $(k\,w')$-th power of the weight-one character of the row-isometry subgroup at $w'$. Let $W$ be the first $\psi$-Whittaker coefficient of $\varphi$, $W(g)=\int \varphi(u(x)g)\psi(-x)\,d\nu(x)$ with $u(x)$ the upper unipotent matrix and $\nu$ the conditioned measure. Writing $D_d$ for $\mathrm{archDerivAt}\,hw\,d$, the derivative at $t=0$ of $t\mapsto \varphi(g\cdot\mathrm{archFlowAt}\,hw\,d\,t)$, with $d\in\{H,E,F^-\}$, the conclusion is threefold: (i) pointwise, the first $\psi$-Whittaker coefficient of $D_H\varphi-i(D_E\varphi+D_{F^-}\varphi)$ equals $D_HW-i(D_EW+D_{F^-}W)$; (ii) the same with all signs $+$; (iii) for every $c_s\in\mathbb{C}$, the function $c_s\cdot\big(D_H\varphi+i(D_E\varphi+D_{F^-}\varphi)\big)$ is again an isotypic cusp form for the same pins, $\xi$, level $\Phi.\mathrm{level}$, $S$ and $\Phi$, satisfies `HasArchCharacterAt₀` at $w$ for $\mathrm{archWeightCharAt}\,hw\,(k\,w+2)$, and, if nonzero, is reproduced by right convolution against some factorizable test function.
--
--   This is the statement that the raising operator $X_+=H+i(E+F^-)$ of the Lie algebra action at a real place carries an isotypic cusp form of weight $k$ to one of weight $k+2$ within the same isotypic space, together with the compatibility of $X_\pm$ with the formation of the first Whittaker coefficient. It is used in the Langlands–Tunnell converse-theorem input, being cited in the construction of Whittaker factorisations for Casimir eigenvectors of minimal weight and of weight zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_isIsotypicCuspFormAt_smul_archRaise_and_whittakerCoefficient_archRaise_archLower.lean

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

theorem LanglandsTunnell.isIsotypicCuspFormAt_smul_archRaise_and_whittakerCoefficient_archRaise_archLower
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ φ)
    (hne : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (k : InfinitePlace ℚ → ℤ)
    (hwt : ∀ (w' : InfinitePlace ℚ) (hw' : w'.IsReal), HasArchCharacterAt₀ ℚ w' (archWeightCharAt hw' (k w')) φ)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW : W = whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1) :

    (∀ p : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ψ (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) 1 p
        = archDerivAt hw ArchDir.H W p - Complex.I * (archDerivAt hw ArchDir.E W p + archDerivAt hw ArchDir.Fm W p)) ∧
    (∀ p : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ψ (archDerivAt hw ArchDir.H φ + Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) 1 p
        = archDerivAt hw ArchDir.H W p + Complex.I * (archDerivAt hw ArchDir.E W p + archDerivAt hw ArchDir.Fm W p)) ∧

    (∀ cs : ℂ,
      IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ξ Φ.level S Φ
          (cs • (archDerivAt hw ArchDir.H φ
            + Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ))) ∧
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w + 2))
          (cs • (archDerivAt hw ArchDir.H φ
            + Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ))) ∧
      (cs • (archDerivAt hw ArchDir.H φ + Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) ≠ 0 →
        ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧
          rightConv ℚ (cs • (archDerivAt hw ArchDir.H φ
            + Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ))) α
            = cs • (archDerivAt hw ArchDir.H φ
              + Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)))) := by sorry
