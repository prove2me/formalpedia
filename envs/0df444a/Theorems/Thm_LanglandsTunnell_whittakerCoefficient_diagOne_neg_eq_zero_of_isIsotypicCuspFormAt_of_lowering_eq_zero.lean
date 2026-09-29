-- Prove2me | Theorems.Thm_LanglandsTunnell_whittakerCoefficient_diagOne_neg_eq_zero_of_isIsotypicCuspFormAt_of_lowering_eq_zero
-- name    : LanglandsTunnell.whittakerCoefficient_diagOne_neg_eq_zero_of_isIsotypicCuspFormAt_of_lowering_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/bfa68fcb-3501-58ff-b02a-e1ee4f4d0204
-- title:
--   Lowering operator forces Whittaker vanishing on the negative torus
-- statement:
--   Work over $\mathbb{Q}$. Fix reals $c,u,d_1<d_2$ and a finite set $T\subset \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and let $D=\bigcup_{x\in T}(\,\cdot\,x)(\mathrm{centreCutSiegelSet}\ c\,u\,d_1\,d_2)$ be the corresponding union of right translates of the centre-cut Siegel set (finite part integral, local height at least $c$, $x$-window at most $u^2$, archimedean determinant norms in $[d_1,d_2]$ at every infinite place); assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ modulo rational points on the left and central ideles on the right. Let $\psi$ be an additive character of $\mathbb{A}_{\mathbb{Q}}$ that is trivial on $\mathbb{Q}$, continuous and non-trivial, whose archimedean part at a real place $w$ is $x\mapsto e^{2\pi i x}$ on ideles supported at $w$ with trivial finite part. Let $\xi$ be a character of the full idele unit group (the component `Z` of the production pins, taken to be $\top$), and let $\varphi$ satisfy `IsIsotypicCuspFormAt` for these pins, $\xi$, an ideal $N$, a finite set $S$ of finite places and a Hecke eigensystem $\Phi$: thus $\varphi$ is a smooth cuspidal automorphic function with central behaviour $\xi$, continuous, invariant under $\mathrm{levelOne}\,N\cap\ker(\mathrm{glArch})$, a Hecke coset eigenfunction with eigenvalue $\Phi.a\,v$ for $v\notin S$, and satisfies the central relation with eigenvalue $(\Phi.\mathrm{toRawCentral}).b\,v$. Assume $\varphi\neq 0$, that $\varphi$ is reproduced by right convolution with some factorizable test function, that $\varphi$ is smooth at $w$ in the sense of `IsArchSmoothAt`, that $\mathrm{archCasimirAt}\,\varphi=(1/4-\nu^2)\varphi$ for some $\nu\in\mathbb{C}$, and that for every real place $w'$ the predicate `HasArchCharacterAt₀` holds for $\varphi$ with the weight character $\mathrm{archWeightCharAt}$ of exponent $k(w')$, for a given $k:\mathrm{InfinitePlace}\,\mathbb{Q}\to\mathbb{Z}$. Assume further that the local component of $\xi$ at $w$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,u_c}(\iota_w(x)/\|x\|)^{a_c}$ for given $u_c\in\mathbb{C}$, $a_c\in\mathbb{Z}$, where $\iota_w$ is the real embedding attached to $w$. Let $W$ be the first $\psi$-Whittaker coefficient of $\varphi$, $W(g)=\int \varphi(n(x)g)\,\psi(-x)\,d\nu(x)$ with $\nu$ the adelic additive Haar measure conditioned on the box $\mathrm{adelicBox}\,\mathbb{Q}$, and assume $W$ is annihilated by the lowering combination at $w$, i.e. $D_HW-i(D_EW+D_{F^-}W)=0$ pointwise. Then for every $g$ with trivial archimedean component, every $t<0$ and every unit $r$ of the completion at $w$ whose image under the isomorphism with $\mathbb{R}$ is $t$, one has $W(\mathrm{diag}(r,1)_w\,g)=0$, where $\mathrm{diag}(r,1)_w$ means the diagonal matrix built from the idele that is $r$ at $w$ and $1$ elsewhere.
--
--   This is the classical statement that the Whittaker function of a vector of lowest weight (holomorphic type) is supported on the positive part of the archimedean split torus: on the other sheet the lowering equation $2yf'-(4\pi y+k)f=0$ forces exponential growth, which a cusp form cannot have. It is used in the construction of the Whittaker factorization for Casimir eigenvectors of minimal weight, one of the analytic inputs to the converse-theorem step of Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_whittakerCoefficient_diagOne_neg_eq_zero_of_isIsotypicCuspFormAt_of_lowering_eq_zero.lean

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

theorem LanglandsTunnell.whittakerCoefficient_diagOne_neg_eq_zero_of_isIsotypicCuspFormAt_of_lowering_eq_zero
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
      ψ φ 1)
    (hlowW : ∀ p : AdelicGL2 (𝓞 ℚ) ℚ,
      archDerivAt hw ArchDir.H W p - Complex.I * (archDerivAt hw ArchDir.E W p + archDerivAt hw ArchDir.Fm W p) = 0)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) (hg : g ∈ finiteAdelicGL2Subgroup ℚ) (t : ℝ) (ht : t < 0)
    (r : (w.Completion)ˣ) (hr : (r : w.Completion) = (ringEquivRealOfIsReal hw).symm t) :
    W (diagOne (archUnitHom w r) * g) = 0 := by sorry
