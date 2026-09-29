-- Prove2me | Theorems.Thm_ModularCurve_two_mul_placeWidthChar_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace_of_prime
-- name    : ModularCurve.two_mul_placeWidthChar_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/78f0c8aa-ccb5-510c-b86f-d39a22ba9ebe
-- title:
--   Moduli place width counts automorphisms of (W,C), all characteristics
-- statement:
--   Let $\kappa$ be an algebraically closed field with decidable equality, let $q'$ be a prime with $\operatorname{char}\kappa=q'$, and let $M'$ be a nonzero natural number with $q'\nmid M'$. Let $W$ be an elliptic Weierstrass curve over $\kappa$ and let $C$ be an additive subgroup of the group of points of the affine model of $W$ which is additively cyclic and satisfies $\operatorname{card} C=M'$. Let $P$ be a place of the intermediate field $\kappa(j(q),j(q^{M'}))\subseteq\kappa((q))$ generated over $\kappa$ by the two series `jqModC` and `jqNModC` — that is, a valuation subring of that field, not equal to the whole field, containing the image of $\kappa$ and a principal ideal ring — and assume that the valuation subring of $P$ is the preimage, under the inclusion of $\kappa(j(q),j(q^{M'}))$ into the full level-$M'$ modular function field, of the valuation subring of the moduli place $\mathrm{moduliPlace}\,\kappa\,M'\,W\,C$ attached to the pair $(W,C)$. Then twice $\mathrm{placeWidthChar}\,q'\,M'\,P$, namely twice the quotient of the characteristic-$q'$ width value $\mathrm{jWidthChar}$ at the residue of the generator `jGeomGen` (the class of $j(q)$) at $P$ by the ramification invariant $\mathrm{placeRamificationJ}\,M'\,P$, equals the number of additive endomorphisms $\iota$ of the points of $W$ which lie in $\mathrm{rationalHomSet}\,\kappa\,W\,W$ (i.e. are zero or rationally represented), admit a two-sided compositional inverse $\iota'$ also lying in $\mathrm{rationalHomSet}\,\kappa\,W\,W$, and satisfy $\iota(C)=C$.
--
--   This identifies the local width of a moduli place on the level-$M'$ modular curve with half the order of the automorphism group of the enhanced elliptic curve $(W,C)$, in every residue characteristic $q'$ not dividing $M'$ — so including $q'=2,3$, where the width table at $j=0$ and $j=1728$ degenerates. It is used in the full-level analysis of Diamond-type rigid charts, where decomposition orders at places above $2$ and $3$ are compared with place widths and with stabiliser cardinalities of level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_two_mul_placeWidthChar_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace_of_prime.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld AlgebraicCurve
open ModularCurve

theorem ModularCurve.two_mul_placeWidthChar_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace_of_prime
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (M' : ℕ) [NeZero M'] (hq'M' : ¬ q' ∣ M')
    (W : WeierstrassCurve κ) [W.IsElliptic] (C : AddSubgroup W.toAffine.Point)
    (hcyc : IsAddCyclic C) (hcard : Nat.card C = M')
    (P : Place κ ↥(modularFunctionFieldC κ M'))
    (hP : P.toValuationSubring =
      (moduliPlace κ M' W C).toValuationSubring.comap
        (IntermediateField.inclusion (modularFunctionFieldC_le_full κ M')).toRingHom) :
    2 * placeWidthChar q' M' P =
      Nat.card {ι : W.toAffine.Point →+ W.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ W W ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ W W, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        C.map ι = C} := by sorry
