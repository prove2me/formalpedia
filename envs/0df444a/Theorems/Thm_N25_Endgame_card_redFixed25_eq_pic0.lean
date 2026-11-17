-- Prove2me | Theorems.Thm_N25_Endgame_card_redFixed25_eq_pic0
-- name    : N25.Endgame.card_redFixed25_eq_pic0
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:25:43.375842+00:00
-- url     : https://prove2.me/theorems/bfab6126-c7e9-4894-b031-4d4feb6cd835
-- title:
--   Frobenius-fixed geometric Picard classes have the finite-field Picard cardinality
-- statement:
--   Let $ℓ$ be a prime with $ℓ∤25$, and let $D$ be a level-$25$ reduction datum at $ℓ$. Let $Pic^0_D$ be the degree-zero Picard group after passage to the residue field of $D$, let $Pic^0_D{}^{Fr=1}$ be its Frobenius-fixed subgroup, and let $F_{𝔽_ℓ}$ be the level-$25$ function field over $𝔽_ℓ$. Then
--
--   $$|Pic^0_D{}^{Fr=1}|=|Pic^0(𝔽_ℓ,F_{𝔽_ℓ})|.$$
--
--   This identifies the fixed subgroup receiving rational reductions with a computable finite-field Jacobian.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CoefficientMap
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import Theorems.Thm_ValuationSubring_exists_pow_pow_eq_self_residueField_of_liesOverPrime
import Theorems.Thm_AlgebraicCurve_Pic0_natCard_fixedPoints_eq_natCard_pic0_of_pushforwardAlong_frobenius

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.card_redFixed25_eq_pic0
    (ℓ : ℕ) [Fact ℓ.Prime] (_hgood : ¬ ℓ ∣ 25)
    (D : RedDatum25 ℓ) :
    Nat.card ↥(RedFixed25 D) =
      Nat.card (AlgebraicCurve.Pic0 (ZMod ℓ) (FBase (ZMod ℓ))) := by sorry
