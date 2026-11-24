-- Prove2me | Theorems.Thm_GlobalTheory_ArcConst_exists_of_localization
-- name    : GlobalTheory.ArcConst.exists_of_localization
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:58:51.738908+00:00
-- url     : https://prove2.me/theorems/bd509981-8177-43b6-9579-3e29e9216817
-- title:
--   Arc Const: exists of localization
-- statement:
--   The Arc Const construction uses the exists of localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L33-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L33-L53

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsIntegralElemOfIsAlgebraicInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
noncomputable section
open GlobalTheory GlobalTheory.ArcConst

theorem GlobalTheory.ArcConst.exists_of_localization {K R S : Type} [Field K] [CharZero K] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] (hM : M ≤ nonZeroDivisors R) (f : K →+* R)
    {s : S} (hs : AlgZ s) : ∃ r : R, algebraMap R S r = s ∧ AlgZ r := by sorry
