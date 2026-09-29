-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_mem_basicOpen_forall_notMem_basicOpen_deckApp
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_mem_basicOpen_forall_notMem_basicOpen_deckApp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/900667e2-7df6-54aa-be3e-9407563a7f4c
-- title:
--   Separating a K-point from its non-trivial n-torsion translates
-- statement:
--   Let $K$ be an algebraically closed field, $A$ a scheme, and $f : A \to \operatorname{Spec} K$ a morphism equipped with a relative group law $L$, i.e. a functorial group structure (multiplication, unit, inverse, associativity, unit laws, left inverses, and naturality under base change) on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over arbitrary $t : T \to \operatorname{Spec} K$; assume $L$ is commutative, that $f$ satisfies `AbelianSchemePropertyBundle` (it is smooth, proper, has connected fibres, and admits a relative group law), and that $f$ is smooth of relative dimension $g$. Let $n$ be a natural number whose image in $K$ is non-zero, and assume that for every $K$-section $x$ with $n \cdot x$ equal to the unit, translation by $x$ followed by the multiplication-by-$n$ endomorphism $[n] =$ `L.schemeNsmul n` equals $[n]$. Let $U$ be an affine open of $A$ and $x$ a section of $f$ over the identity of $\operatorname{Spec} K$ whose value $z$ at the closed point of $\operatorname{Spec} K$ lies in $[n]^{-1}U$. Then there is a section $a \in \Gamma(A, [n]^{-1}U)$ with $z \in D(a)$ such that for every $n$-torsion section $P$ other than the unit, $z \notin D\bigl(\mathrm{deckApp}(n,P)(a)\bigr)$, where $\mathrm{deckApp}(n,P)$ is the map on $\Gamma(A,[n]^{-1}U)$ induced by translation by $P$ via the hypothesis that it preserves $[n]^{-1}U$.
--
--   This is the separation step used to produce a local generator: on the affine chart $[n]^{-1}U$ one finds a function non-vanishing at $z$ but vanishing at all the translates $z \cdot P$ by non-trivial $n$-torsion points, so that the deck transformations of $[n]$ act on a distinguished neighbourhood in a controlled way. It is cited in the construction of the eigen-subdatum on an affine open, `exists_affineOpens_isUnit_eigenSubdatum`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_mem_basicOpen_forall_notMem_basicOpen_deckApp.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_mem_basicOpen_forall_notMem_basicOpen_deckApp
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (n : ℕ) (hn : (n : K) ≠ 0)
    (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n)
    (U : A.affineOpens) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f)
    (hx : x.1.base (IsLocalRing.closedPoint K) ∈ (L.schemeNsmul n) ⁻¹ᵁ U.1) :
    ∃ a : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U.1),
      x.1.base (IsLocalRing.closedPoint K) ∈ A.basicOpen a ∧
      ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f)
        (hP : P ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n),
        P ≠ L.one (𝟙 (Spec (CommRingCat.of K))) →
          x.1.base (IsLocalRing.closedPoint K) ∉ A.basicOpen ((L.deckApp n P (hG P hP) U.1).hom a) := by sorry
