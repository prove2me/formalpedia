-- Prove2me | Theorems.Thm_GlobalTheory_SmoothNormal_isNormalScheme_of_smoothOfRelativeDimension
-- name    : GlobalTheory.SmoothNormal.isNormalScheme_of_smoothOfRelativeDimension
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:23:57.536388+00:00
-- url     : https://prove2.me/theorems/55bdf4bb-b988-46b1-a3a4-0ffd40ffe711
-- title:
--   Smooth Normal: is Normal Scheme of smooth Of Relative Dimension
-- statement:
--   The Smooth Normal construction uses the is Normal Scheme of smooth Of Relative Dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormalSchemeOfSmoothOverNormal.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormalSchemeOfSmoothOverNormal.lean#L9-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormalSchemeOfSmoothOverNormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.SmoothNormal

theorem GlobalTheory.SmoothNormal.isNormalScheme_of_smoothOfRelativeDimension :
    ∀ (B Y : Scheme.{0}) [IsLocallyNoetherian B] (π : Y ⟶ B) (n : ℕ) [SmoothOfRelativeDimension n π],
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := by sorry
