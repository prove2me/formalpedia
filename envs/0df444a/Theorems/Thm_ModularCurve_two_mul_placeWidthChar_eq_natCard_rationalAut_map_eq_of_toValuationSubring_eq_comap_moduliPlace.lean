-- Prove2me | Theorems.Thm_ModularCurve_two_mul_placeWidthChar_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace
-- name    : ModularCurve.two_mul_placeWidthChar_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/da9a5781-6057-5b71-b84b-250fd5e281fb
-- title:
--   Twice the characteristic width of a moduli place counts level-preserving automorphisms
-- statement:
--   Let $\kappa$ be an algebraically closed field, $q'$ a prime with $5 \le q'$ and $\operatorname{char}\kappa = q'$, and let $M'$ be a nonzero natural number with $q' \nmid M'$. Let $W$ be a Weierstrass curve over $\kappa$ which is elliptic, and let $C$ be an additive subgroup of the group of affine points $W(\kappa)$ which is additively cyclic and satisfies $\#C = M'$. Let $P$ be a place of the intermediate field $\kappa(j(q), j(q^{M'})) \subseteq \kappa((q))$ generated over $\kappa$ by the Laurent series `jqModC` and `jqNModC` — that is, a valuation subring of that field containing the image of $\kappa$, proper, and a principal ideal ring — and assume that the valuation subring of $P$ is the preimage, under the inclusion of $\kappa(j(q), j(q^{M'}))$ into the full modular function field, of the valuation subring of the moduli place `moduliPlace` attached to the pair $(W, C)$. Then twice the characteristic-aware width $\operatorname{placeWidthChar}_{q', M'}(P)$, namely `jWidthChar` at $q'$ of the residue value of $P$ at the generator $j(q)$ divided by the ramification invariant `placeRamificationJ`, equals the number of additive endomorphisms $\iota$ of $W(\kappa)$ such that $\iota$ lies in `rationalHomSet` (i.e. $\iota = 0$ or $\iota$ is rationally represented over $\kappa$), $\iota$ has a two-sided inverse also lying in `rationalHomSet`, and $\iota(C) = C$.
--
--   This is the local computation, at a place of the level-$M'$ modular function field coming from an enhanced elliptic curve $(W, C)$ in characteristic $q' \ge 5$, identifying twice the width of the place with the order of the group of automorphisms of $W$ preserving the cyclic subgroup $C$. It is the form of that identity phrased in the characteristic-aware width, used by the statements about the special fibre of the modular curve at full level: the genus and component count identities and the rigid-analytic chart statements that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_two_mul_placeWidthChar_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace.lean

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

theorem ModularCurve.two_mul_placeWidthChar_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] (hq5 : 5 ≤ q')
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
