-- Prove2me | Theorems.Thm_GlobalTheory_FinTypeIntCatenary_isCM_localization_int
-- name    : GlobalTheory.FinTypeIntCatenary.isCM_localization_int
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:36.730178+00:00
-- url     : https://prove2.me/theorems/f059b45b-82df-457f-ad50-8465ab2ffa9c
-- title:
--   Fin Type Int Catenary: is CM localization int
-- statement:
--   The Fin Type Int Catenary construction uses the is CM localization int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeightMaximalLePrimeAddDim.lean#L83-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeightMaximalLePrimeAddDim.lean#L83-L98

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

theorem GlobalTheory.FinTypeIntCatenary.isCM_localization_int (p : Ideal ℤ) [p.IsMaximal] :
    IsCM (Localization.AtPrime p) ∧ ringKrullDim (Localization.AtPrime p) = 1 := by sorry
