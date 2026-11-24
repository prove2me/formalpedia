-- Prove2me | Theorems.Thm_GlobalTheory_FinTypeIntCatenary_isCM_atPrime_of_le
-- name    : GlobalTheory.FinTypeIntCatenary.isCM_atPrime_of_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:26:12.474821+00:00
-- url     : https://prove2.me/theorems/f146af7c-1781-4fa8-85ee-d59144db32a1
-- title:
--   Fin Type Int Catenary: is CM at Prime of le
-- statement:
--   The Fin Type Int Catenary construction uses the is CM at Prime of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeightMaximalLePrimeAddDim.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeightMaximalLePrimeAddDim.lean#L10-L27

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

theorem GlobalTheory.FinTypeIntCatenary.isCM_atPrime_of_le {S : Type*} [CommRing S] (𝔓 𝔑 : Ideal S) [𝔓.IsPrime] [𝔑.IsPrime]
    (hle : 𝔓 ≤ 𝔑) (h : IsCM (Localization.AtPrime 𝔑)) : IsCM (Localization.AtPrime 𝔓) := by sorry
