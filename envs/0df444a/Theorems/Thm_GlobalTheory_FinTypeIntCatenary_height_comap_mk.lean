-- Prove2me | Theorems.Thm_GlobalTheory_FinTypeIntCatenary_height_comap_mk
-- name    : GlobalTheory.FinTypeIntCatenary.height_comap_mk
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:30.888046+00:00
-- url     : https://prove2.me/theorems/7c720572-eec1-4d05-8c21-04d92a689c9b
-- title:
--   Fin Type Int Catenary: height comap mk
-- statement:
--   The Fin Type Int Catenary construction uses the height comap mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeightMaximalLePrimeAddDim.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeightMaximalLePrimeAddDim.lean#L29-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeightMaximalLePrimeAddDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinTypeIntCatenary
open ReciprocityTheory.CA

theorem GlobalTheory.FinTypeIntCatenary.height_comap_mk {S : Type*} [CommRing S] (Q : Ideal S) [Q.IsPrime] (J : Ideal (S ⧸ Q))
    [J.IsPrime] (h : IsCM (Localization.AtPrime (J.comap (Ideal.Quotient.mk Q)))) :
    (J.comap (Ideal.Quotient.mk Q)).height = Q.height + J.height := by sorry
