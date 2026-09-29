-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_map_restrictNormalHom_upperRamificationGroup_eq
-- name    : NumberField.PlaceDecomp.map_restrictNormalHom_upperRamificationGroup_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/4eec332a-bdc1-5e7c-92a2-ba636acba76e
-- title:
--   Herbrand's theorem for upper ramification groups in a tower
-- statement:
--   Let $E \subseteq L \subseteq F$ be number fields, with $F$ an algebra over $L$ and over $E$ compatibly (scalar tower), $F/E$ Galois and $L/E$ normal. Let $w$ be a height-one prime of $\mathcal O_F$ and let $u$ be a rational number with $0 \le u$. Write $A_w$ for the valuation subring of $F$ attached to the $w$-adic valuation and $D_w \le F \simeq_{\mathrm{alg}[E]} F$ for its decomposition subgroup; for a rational $v$, the upper ramification group of $A_w$ at $v$ is the subgroup of $D_w$ given by the lower ramification group of index $n$, where $n$ is the least natural number with $v \le \varphi(n)$ for the Herbrand function of the action of $D_w$ on $A_w$, the lower ramification group of index $i$ being the inertia subgroup attached to the ideal $\mathfrak m_{A_w}^{\,i+1}$. The same notions are taken for the prime $w \cap \mathcal O_L$ of $\mathcal O_L$ and its valuation subring of $L$. The assertion is that the image of the upper ramification group at $u$ of $A_w$, viewed inside $F \simeq_{\mathrm{alg}[E]} F$, under restriction of automorphisms to $L$ equals the upper ramification group at $u$ of the valuation subring of $L$ at $w \cap \mathcal O_L$, viewed inside $L \simeq_{\mathrm{alg}[E]} L$.
--
--   This is Herbrand's theorem on the compatibility of the upper ramification filtration with passage to a normal subextension, stated for places of number fields: upper ramification groups restrict onto upper ramification groups at the same parameter. It feeds the local computation of ramification filtrations used in the statement [`NumberField.PlaceDecomp.exists_forall_upperRamificationGroup_smul_eq_and_finprod_quotient_smul_eq_of_valuation_sub_one_le`](thm.html#NumberField.PlaceDecomp.exists_forall_upperRamificationGroup_smul_eq_and_finprod_quotient_smul_eq_of_valuation_sub_one_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_map_restrictNormalHom_upperRamificationGroup_eq.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.map_restrictNormalHom_upperRamificationGroup_eq
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [Normal E L]
    (w : HeightOneSpectrum (𝓞 F)) (u : ℚ) (hu : 0 ≤ u) :
    (((((w.valuation F).valuationSubring).upperRamificationGroup E u).map
        (((w.valuation F).valuationSubring).decompositionSubgroup E).subtype).map
        (AlgEquiv.restrictNormalHom L : (F ≃ₐ[E] F) →* (L ≃ₐ[E] L))) =
      ((((w.under (𝓞 L)).valuation L).valuationSubring).upperRamificationGroup E u).map
        ((((w.under (𝓞 L)).valuation L).valuationSubring).decompositionSubgroup E).subtype := by sorry
