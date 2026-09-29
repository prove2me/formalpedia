-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translate_of_comp_schemeNsmul_eq
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translate_of_comp_schemeNsmul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/a879e61a-3be6-54ca-adcf-7d8b5d8420c2
-- title:
--   Morphisms agreeing after [n] differ locally by n-torsion translation
-- statement:
--   Let $K$ be an algebraically closed field and let $f : A \to \operatorname{Spec} K$ be a morphism of schemes equipped with a relative group law $L$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-points over each $t : T \to \operatorname{Spec} K$, natural in $T$; assume $L$ is commutative, and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$, namely that $f$ is smooth and proper, that every fibre $f^{-1}(s)$ over a point $s$ of $\operatorname{Spec} K$ is connected, and that a relative group law on $f$ exists. Assume further that $f$ is smooth of relative dimension $g$, and let $n$ be a natural number with $n \neq 0$ in $K$. Write $L.\mathrm{schemeNsmul}\ n : A \to A$ for the morphism obtained by forming the $n$-fold group-law sum of the identity $A$-point with itself. Then for any scheme $Z$ and any two morphisms $g_1, g_2 : Z \to A$ with $g_1$ followed by $[n]$ equal to $g_2$ followed by $[n]$, there is a family of open subschemes $U_P \subseteq Z$ indexed by the set of sections $P : \operatorname{Spec} K \to A$ of $f$ whose $n$-fold group-law multiple is the identity section, such that $\bigsqcup_P U_P = \top$, i.e. the $U_P$ cover $Z$, and such that for each $P$ the restrictions to $U_P$ satisfy $g_2 = T_P \circ g_1$, where $T_P = L.\mathrm{translate}\ P$ is the group-law translation by $P$.
--
--   This is the scheme-theoretic form of the classical statement that, for $n$ invertible on the base, multiplication by $n$ on an abelian variety is a finite étale cover which is a torsor under the finite group scheme $A[n]$: two maps into $A$ with the same image under $[n]$ differ, locally on the source, by translation by an $n$-torsion point. It is used in the analysis of the $n$-torsion of Jacobians, being cited by [`GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_smul_eigenOne`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_smul_eigenOne) and by [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_mem_torsionSubset_translate_base_eq_of_schemeNsmul_base_eq`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_mem_torsionSubset_translate_base_eq_of_schemeNsmul_base_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translate_of_comp_schemeNsmul_eq.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_GoodReductionJacobian_NsmulEigenSubdatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translate_of_comp_schemeNsmul_eq
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (n : ℕ) (hn : (n : K) ≠ 0)
    {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ A) (h : g₁ ≫ L.schemeNsmul n = g₂ ≫ L.schemeNsmul n) :
    ∃ U : L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n → Z.Opens, ⨆ P, U P = ⊤ ∧
      ∀ P, (U P).ι ≫ g₂ = (U P).ι ≫ g₁ ≫ L.translate P.1 := by sorry
