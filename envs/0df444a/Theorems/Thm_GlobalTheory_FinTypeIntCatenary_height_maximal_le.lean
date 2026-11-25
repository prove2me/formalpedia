-- Prove2me | Theorems.Thm_GlobalTheory_FinTypeIntCatenary_height_maximal_le
-- name    : GlobalTheory.FinTypeIntCatenary.height_maximal_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:51.379661+00:00
-- url     : https://prove2.me/theorems/7ea13037-2a81-4b07-874d-52d1b42fc7aa
-- title:
--   Fin Type Int Catenary: height maximal le
-- statement:
--   The Fin Type Int Catenary construction uses the height maximal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeightMaximalLePrimeAddDim.lean#L173-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeightMaximalLePrimeAddDim.lean#L173-L188

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

theorem GlobalTheory.FinTypeIntCatenary.height_maximal_le (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
    (P M : Ideal A) [P.IsPrime] [M.IsMaximal] :
    (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by sorry
