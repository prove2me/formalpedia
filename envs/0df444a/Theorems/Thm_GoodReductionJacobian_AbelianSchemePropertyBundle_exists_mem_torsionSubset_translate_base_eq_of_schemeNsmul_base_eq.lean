-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_mem_torsionSubset_translate_base_eq_of_schemeNsmul_base_eq
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_mem_torsionSubset_translate_base_eq_of_schemeNsmul_base_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/7f5e7d7a-e852-5516-b4e9-8349cc746b4e
-- title:
--   n-torsion translations act transitively on fibres of [n]
-- statement:
--   Let $K$ be an algebraically closed field (in a fixed universe), $A$ a scheme and $f : A \to \operatorname{Spec} K$ a morphism, and let $L$ be a relative group law on $f$: a group structure on the sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for every $t : T \to \operatorname{Spec} K$ (multiplication, unit, inverse, with associativity, unit and inverse laws), natural in base changes $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume $L$ is commutative, and that $f$ satisfies the bundle of properties `AbelianSchemePropertyBundle`: $f$ is smooth and proper, every fibre $f^{-1}(s)$ of the underlying map is connected, and $f$ admits a relative group law. Let $g : \mathbb{N}$ with $f$ smooth of relative dimension $g$, and let $n : \mathbb{N}$ with $n \neq 0$ in $K$. Let $z, z'$ be points of the underlying space of $A$ whose images agree under the map on points of `L.schemeNsmul n`, the endomorphism $A \to A$ given by the first component of the $n$-fold $L$-sum of the identity section $\mathbb{1}_A$ of $f$ over $f$. Then there is a section $P : \operatorname{Spec} K \to A$ over the identity of $\operatorname{Spec} K$ with $n$-fold $L$-sum equal to the unit section, i.e. $P$ lies in `L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n`, such that the translation endomorphism `L.translate P` (the first component of the $L$-product of $\mathbb{1}_A$ with $f$ followed by $P$) carries $z$ to $z'$ on points.
--
--   This is the pointwise transitivity statement for the action of the $n$-torsion on the fibres of multiplication by $n$ on an abelian scheme over an algebraically closed field: two points of $A$ with the same image under $[n]$ differ by an $n$-torsion translation, here formulated for arbitrary (not necessarily closed) points of the underlying space. It feeds the construction of affine opens on which an eigen-subdatum becomes invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_mem_torsionSubset_translate_base_eq_of_schemeNsmul_base_eq.lean

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

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_mem_torsionSubset_translate_base_eq_of_schemeNsmul_base_eq
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (n : ℕ) (hn : (n : K) ≠ 0)
    (z z' : A) (h : (L.schemeNsmul n).base z = (L.schemeNsmul n).base z') :
    ∃ P ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n, (L.translate P).base z = z' := by sorry
