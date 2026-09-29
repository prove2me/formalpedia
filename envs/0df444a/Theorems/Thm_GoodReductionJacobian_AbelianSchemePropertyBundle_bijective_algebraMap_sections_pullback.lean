-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_algebraMap_sections_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/ff6e72cd-94a5-5319-bf21-2ddb7de27d88
-- title:
--   f_*mathcal O_A=𝒪 universally for abelian schemes
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f \colon A \to \operatorname{Spec} R$ a morphism satisfying the bundle of properties `AbelianSchemePropertyBundle R f`, namely: $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} R$ the fibre $f^{-1}(\{s\})$ (the preimage under the map on underlying spaces) is connected and non-empty, and there exists a relative group law on $f$ over $R$, i.e. functorial group operations (multiplication, unit, inverse, with associativity, unit and inverse laws and compatibility with base change along morphisms of $R$-schemes) on the sets of sections $T \to A$ over $\operatorname{Spec} R$ for all schemes $T$ over $\operatorname{Spec} R$. Let $T$ be a commutative $R$-algebra. Equip $\Gamma(A \times_{\operatorname{Spec} R} \operatorname{Spec} T, \mathcal O)$ with the $T$-algebra structure coming from the ring map $T \cong \Gamma(\operatorname{Spec} T, \mathcal O) \to \Gamma(A \times_{\operatorname{Spec} R} \operatorname{Spec} T, \mathcal O)$ induced by the second projection, where the base change is along $\operatorname{Spec}$ of $R \to T$. The assertion is that this structure map is bijective.
--
--   This is the statement that $f_*\mathcal O_A = \mathcal O$ holds universally for an abelian scheme $A \to \operatorname{Spec} R$, the degree-zero cohomology-and-base-change (Stein factorisation) input behind rigidity. It serves as the global-sections hypothesis in the rigidity, gluing and descent results for rigidified line bundles and in the lemmas on polarisations and framed polarised abelian schemes that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_algebraMap_sections_pullback
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (T : Type u) [CommRing T] [Algebra R T] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R T)) ⊤
    Function.Bijective (algebraMap T Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R T), ⊤)) := by sorry
