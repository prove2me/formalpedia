-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_CubicInductionForm_twist_det_package
-- name    : LanglandsTunnell.CubicInduction.CubicInductionForm.twist_det_package
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/62da2e34-5c69-57a4-952a-5cc5421655f8
-- title:
--   Twisting a cubic induction form by a character of the determinant
-- statement:
--   Let $K$ be a number field whose ring of integers is an integral $\mathcal O_{\mathbb Q}$-algebra, let `pins` be a carrier-pin package over $\mathbb Q$, let $\psi$ be an additive character of the adeles of $\mathbb Q$ with values in $\mathbb C$, let $\nu$ be a character of the ideles of $K$, and let $F$ be a cubic induction form for $(K,\mathtt{pins},\psi,\nu)$, with fields `form`, `whittaker`, `whittakerLoc`, `whittakerArch`, `dualWhittaker` and the accompanying automorphy, cuspidality, Whittaker, expansion, factorisation, sphericity and growth axioms. Let $\chi_{\mathbb A}$ be a homomorphism from the ideles of $\mathbb Q$ to $\mathbb C^\times$ which is an admissible twist (trivial on principal ideles, continuous and of absolute value $1$ everywhere) and whose component at each real place is trivial in the sense that $\chi_{\mathbb A}$ restricted to the units of that completion is given by the formula of `IsArchCompAt` with exponents $0,0$. Put $\Theta(x)=\chi_{\mathbb A}(\det x)\,F.\mathrm{form}(x)$, $W^{\chi}(x)=\chi_{\mathbb A}(\det x)\,F.\mathrm{whittaker}(x)$ and $\widetilde W^{\chi}(x)=\chi_{\mathbb A}(\det x)^{-1}F.\mathrm{dualWhittaker}(x)$ on $\mathrm{GL}_3$ of the adeles of $\mathbb Q$. The conclusion is a conjunction of eleven assertions: $\Theta(\gamma g)=\Theta(g)$ for every $\gamma\in\mathrm{GL}_3(\mathbb Q)$ embedded adelically; $W^{\chi}$ transforms by $\psi(x+y)$ and $\widetilde W^{\chi}$ by $\psi^{-1}(x+y)$ under left translation by the upper unipotent matrix with entries $x,y,z$; for every $g$, the family $i\mapsto W^{\chi}(\mathtt{mirabolicTranslate}\,i\cdot g)$, indexed by right cosets of the unipotent subgroup in $\mathrm{GL}_2(\mathbb Q)$, has sum $\Theta(g)$, and the corresponding family for $\widetilde W^{\chi}$ has sum $\Theta((g^{-1})^{\mathsf T})$; continuity of `form`, `whittaker`, `dualWhittaker` transfers to $\Theta$, $W^{\chi}$, $\widetilde W^{\chi}$ respectively; the gauge-majorisation property `IsGaugeMajorised3` (vanishing outside a root-level region together with decay by $C/(\mathtt{rootSizeProd}^t(1+\mathtt{archRootSum})^N)$) transfers from `whittaker` to $W^{\chi}$ and from `dualWhittaker` to $\widetilde W^{\chi}$; at each finite place $v$ the function $y\mapsto \chi_{\mathbb A,v}(\det y)F.\mathrm{whittakerLoc}_v(y)$ satisfies the $\psi_v$-Whittaker law; and finally, for every $g$ and every finite set $T$ of finite places containing all places that are bad for $\nu$ (ramified in $K$, or with $\nu$ ramified at some prime of $K$ above) and all places where $\chi_{\mathbb A}$ is ramified, and such that $g_v$ lies in the local maximal compact subgroup for $v\notin T$, one has $W^{\chi}(g)=F.\mathrm{whittakerArch}(g_\infty)\prod_{v\in T}\chi_{\mathbb A,v}(\det g_v)F.\mathrm{whittakerLoc}_v(g_v)$, with the archimedean factor unchanged.
--
--   This is the compatibility of the cubic automorphic induction package with twisting by $\chi_{\mathbb A}\circ\det$: each structural property of the induced $\mathrm{GL}_3$ form is shown to persist for the twisted form, Whittaker function and dual Whittaker function. It feeds the construction of the twisted cubic induction datum and the local zeta-integral/functional-equation statements attached to it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_CubicInductionForm_twist_det_package.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.CubicInductionForm.twist_det_package
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : AutomorphicForm.CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (F : CubicInductionForm K pins ψ ν)
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (_hχinf : ∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ χA v 0 0) :

    (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.form x) (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.form x) g) ∧

    IsGL3PsiWhittakerFn ψ (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.whittaker x) ∧
    IsGL3PsiWhittakerFn ψ⁻¹ (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)⁻¹ * F.dualWhittaker x) ∧

    (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      HasSum (fun i : MirabolicIndex ℚ => (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.whittaker x) (mirabolicTranslate i * g)) ((fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.form x) g)) ∧
    (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      HasSum (fun i : MirabolicIndex ℚ => (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)⁻¹ * F.dualWhittaker x) (mirabolicTranslate i * g)) (dualForm (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.form x) g)) ∧

    (Continuous F.form → Continuous (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.form x)) ∧
    (Continuous F.whittaker → Continuous (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.whittaker x)) ∧
    (Continuous F.dualWhittaker → Continuous (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)⁻¹ * F.dualWhittaker x)) ∧

    (IsGaugeMajorised3 ℚ F.whittaker → IsGaugeMajorised3 ℚ (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.whittaker x)) ∧
    (IsGaugeMajorised3 ℚ F.dualWhittaker → IsGaugeMajorised3 ℚ (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)⁻¹ * F.dualWhittaker x)) ∧

    (∀ v : HeightOneSpectrum (𝓞 ℚ), IsGL3PsiWhittakerFn (psiLoc ψ v) (fun y : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * F.whittakerLoc v y)) ∧

    (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))),
      (∀ v, IsBadPlace K ν v → v ∈ T) →
      (∀ v, ¬ IsUnramifiedCharAt χA v → v ∈ T) →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.whittaker x) g =
        F.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) *
          ∏ v ∈ T, (fun y : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * F.whittakerLoc v y) (componentAt3 (𝓞 ℚ) ℚ v g)) := by sorry
