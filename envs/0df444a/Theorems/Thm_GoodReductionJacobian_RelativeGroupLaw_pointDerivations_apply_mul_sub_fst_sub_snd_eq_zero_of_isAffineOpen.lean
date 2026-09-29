-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero_of_isAffineOpen
-- name    : GoodReductionJacobian.RelativeGroupLaw.pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/c568c84e-ac63-5680-a738-5c61f9b8d45e
-- title:
--   Point derivations at (e,e) kill μ^sharp a-p₁^sharp a-p₂^sharp a
-- statement:
--   Let $k$ be a field, $A$ a scheme and $f \colon A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law on $f$ over $k$: an assignment, for every scheme $T$ and every $t \colon T \to \operatorname{Spec} k$, of multiplication, unit and inversion operations on the set of $\phi \colon T \to A$ with $\phi \circ f = t$ (written $\varphi \gg f = t$), satisfying associativity, the two unit laws, left inverse cancellation, and naturality of multiplication under base change along $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Write $p_1, p_2$ for the two projections of $P = A \times_{\operatorname{Spec} k} A$ (the pullback of $f$ along itself) and $\mu$ for the underlying morphism $P \to A$ of $L.\mathrm{mul}$ applied, over $t = p_1$ followed by $f$, to the two $P$-points $p_1$ and $p_2$ (the latter admissible by the pullback condition). Let $U_e \subseteq A$ be an open with $U_e$ affine, and let $U' \subseteq P$ be an affine open contained in each of $p_1^{-1}U_e$, $p_2^{-1}U_e$ and $\mu^{-1}U_e$. Let $e_P \colon \operatorname{Spec} k \to U'$ be a point such that $e_P$ followed by the inclusion $U' \hookrightarrow P$ and then by either projection equals the underlying morphism of $L.\mathrm{one}$ at the identity of $\operatorname{Spec} k$. Let $M$ be a $k$-vector space, and let $D$ be a point derivation at $e_P$ with values in $M$: regarding $\Gamma(P, U')$ as a $k$-algebra via the structure morphism $p_1$ followed by $f$, and letting $\mathrm{ev} \colon \Gamma(P, U') \to k$ be evaluation at $e_P$ (the composite of the inverse of the top isomorphism of $U'$, the global sections map of $e_P$, and the $\Gamma\!-\!\operatorname{Spec}$ isomorphism), $D$ is a $k$-linear map $\Gamma(P, U') \to M$ with $D(ab) = \mathrm{ev}(a)\,D(b) + \mathrm{ev}(b)\,D(a)$. Then for every $a \in \Gamma(A, U_e)$ one has $D(\mu^\sharp a|_{U'} - p_1^\sharp a|_{U'} - p_2^\sharp a|_{U'}) = 0$.
--
--   This is the statement that the differential of a group law at the unit is addition: on tangent vectors at $(e,e)$ the comultiplication $\mu^\sharp$ acts as $p_1^\sharp + p_2^\sharp$. It is used in the construction of the obstruction two-cocycle attached to an abelian scheme property bundle, where the difference of sections above must be annihilated by point derivations at the unit section.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian Scheme.TwoAffineOpenCover

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero_of_isAffineOpen
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (Ue : A.Opens) (hUe : IsAffineOpen Ue)
    (U' : (pullback f f).Opens) (hU' : IsAffineOpen U')
    (hU₁ : U' ≤ pullback.fst f f ⁻¹ᵁ Ue) (hU₂ : U' ≤ pullback.snd f f ⁻¹ᵁ Ue)
    (hUμ : U' ≤ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 ⁻¹ᵁ Ue)
    (eP : Spec (CommRingCat.of k) ⟶ (U' : Scheme.{u}))
    (heP₁ : eP ≫ U'.ι ≫ pullback.fst f f = (L.one (𝟙 _)).1) (heP₂ : eP ≫ U'.ι ≫ pullback.snd f f = (L.one (𝟙 _)).1)
    (M : Type u) [AddCommGroup M] [Module k M]
    (D : letI := algebraOfHom (pullback.fst f f ≫ f) U'
      ↥(Algebra.PointDerivations k Γ(pullback f f, U')
          ((U'.topIso.inv ≫ eP.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom) M))
    (a : Γ(A, Ue)) :
    D.1 (((pullback f f).presheaf.map (homOfLE hUμ).op).hom
            (((L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1.app Ue).hom a) -
          ((pullback f f).presheaf.map (homOfLE hU₁).op).hom (((pullback.fst f f).app Ue).hom a) -
          ((pullback f f).presheaf.map (homOfLE hU₂).op).hom (((pullback.snd f f).app Ue).hom a)) = 0 := by sorry
