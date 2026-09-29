-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_one_eq_one_of_isBadPlace
-- name    : LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_whittakerLoc_one_eq_one_of_isBadPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/390128f9-09d6-5203-9e1b-bc63637ddfc7
-- title:
--   Normalising cubic induction data at bad places
-- statement:
--   Let $K$ be a number field whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, let $\psi$ be a continuous additive character of the adeles of $\mathbb{Q}$ with values in $\mathbb{C}$, let $\mu$ be a character of the idele group of $K$, and let $D$, $U$, $\mathrm{gen}$ be the data entering `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`, the carrier pins on $\mathrm{GL}_2$ over $\mathbb{Q}$ formed from the adelic Borel structure and Haar measure, the set $D$, the full central subgroup, the level subgroups $U$, the generators $\mathrm{gen}$, and the adelic additive Haar measure conditioned on the adelic box. Let $X$ be cubic induction data, i.e. a tuple consisting of a function `form` on $\mathrm{GL}_3$ of the adeles, a global Whittaker function, local Whittaker functions $X.\mathrm{whittakerLoc}\,v$ on $\mathrm{GL}_3(\mathbb{Q}_v)$, an archimedean Whittaker function, a central character on the ideles, and a dual Whittaker function. Assume: $X$ satisfies the predicate `IsCubicInductionDataOn` for $(K,\psi,\mu)$ relative to these pins and to the set $S=\{v \mid \mathrm{IsBadPlace}\,K\,\mu\,v\}$ of places $v$ that are ramified in $K$ or twist-ramified above $K$ with respect to $\mu$ — a package of conditions summarised here comprising left invariance of the form under the rational points and the central character law, the idele-class property of $X.\mathrm{centralChar}$, cuspidality along the two maximal parabolics, the identification of $X.\mathrm{whittaker}$ with the Whittaker integral of the form against $\psi$ and its $\psi$-equivariance, the mirabolic expansion of the form, the $\psi_v$-equivariance and multiplicity-one property of each local factor, the factorisation of $X.\mathrm{whittaker}$ into the archimedean factor times a finite product of local factors, induced sphericality and level invariance outside $S$, moderate growth, $K$-finiteness, the moment and half-plane conditions, and the corresponding statements for $X.\mathrm{dualWhittaker}$ and the dual form; $X.\mathrm{form}$, $X.\mathrm{whittaker}$, $X.\mathrm{dualWhittaker}$ are continuous; $X.\mathrm{whittaker}$ and $X.\mathrm{dualWhittaker}$ are gauge-majorised in the sense of `IsGaugeMajorised3` (vanishing outside a root level and a prescribed decay there); $X.\mathrm{form} \neq 0$ and $X.\mathrm{whittakerArch} \neq 0$; a finite set $T$ of finite places containing all bad places; at every bad place the local Whittaker function is right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$; and at every bad place it transforms under the scalar matrices by the local component of $X.\mathrm{centralChar}$. The conclusion is the existence of cubic induction data $Y$ satisfying `IsCubicInductionDataOn` for the same $(K,\psi,\mu)$, pins and bad-place set, with $Y.\mathrm{form} \neq 0$, with $Y.\mathrm{whittakerLoc}\,w\,(1)=1$ at every bad place $w$, with $Y.\mathrm{whittakerLoc}\,v = X.\mathrm{whittakerLoc}\,v$ at every place that is not bad, with $\mathrm{gl3CyclicSubspace}(Y.\mathrm{whittakerLoc}\,v) = \mathrm{gl3CyclicSubspace}(X.\mathrm{whittakerLoc}\,v)$ (equality of the spans of the right translates) at every place, with the same archimedean Whittaker function and the same central character as $X$, with continuous form, Whittaker and dual Whittaker functions, with both Whittaker functions gauge-majorised, and with the open right invariance and the scalar transformation law under the local component of $Y.\mathrm{centralChar}$ again holding at every bad place.
--
--   This is the normalisation step for cubic induction data: each local Whittaker function at a bad place is replaced by a right translate, rescaled so that its value at the identity is $1$, without changing the span of its right translates, the archimedean factor, the central character or the non-vanishing of the form. It is used in the identification of the local factors at the bad places, where the local zeta integrals of the normalised data are computed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_one_eq_one_of_isBadPlace.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_whittakerLoc_one_eq_one_of_isBadPlace
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      {v | IsBadPlace K μ v} X)
    (hcont : Continuous X.form) (hcontW : Continuous X.whittaker)
    (hcontW' : Continuous X.dualWhittaker)
    (hmaj : IsGaugeMajorised3 ℚ X.whittaker) (hmaj' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hform : X.form ≠ 0) (harch : X.whittakerArch ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (hT : ∀ v, IsBadPlace K μ v → v ∈ T)
    (hsm : ∀ v, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g)
    (hcen : ∀ v, IsBadPlace K μ v → ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      X.whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
        ((NumberField.TateGlobal.localChar X.centralChar v t : ℂˣ) : ℂ) * X.whittakerLoc v h) :
    ∃ Y : CubicInductionData,
      IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} Y ∧
      Y.form ≠ 0 ∧
      (∀ w, IsBadPlace K μ w → Y.whittakerLoc w 1 = 1) ∧
      (∀ v, ¬ IsBadPlace K μ v → Y.whittakerLoc v = X.whittakerLoc v) ∧
      (∀ v, gl3CyclicSubspace (Y.whittakerLoc v) = gl3CyclicSubspace (X.whittakerLoc v)) ∧
      Y.whittakerArch = X.whittakerArch ∧ Y.centralChar = X.centralChar ∧
      Continuous Y.form ∧ Continuous Y.whittaker ∧ Continuous Y.dualWhittaker ∧
      IsGaugeMajorised3 ℚ Y.whittaker ∧ IsGaugeMajorised3 ℚ Y.dualWhittaker ∧
      (∀ v, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, Y.whittakerLoc v (g * k) = Y.whittakerLoc v g) ∧
      (∀ v, IsBadPlace K μ v → ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
        Y.whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((NumberField.TateGlobal.localChar Y.centralChar v t : ℂˣ) : ℂ) * Y.whittakerLoc v h) := by sorry
