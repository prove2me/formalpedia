-- Prove2me | Theorems.Thm_GlobalTheory_FlagDim_card_pairs_lt
-- name    : GlobalTheory.FlagDim.card_pairs_lt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:32:00.230295+00:00
-- url     : https://prove2.me/theorems/32fe72eb-53ba-4b14-9f92-91707ac0a004
-- title:
--   Flag Dim: card pairs lt
-- statement:
--   The Flag Dim construction uses the card pairs lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/DimAddCardFlagVar.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/DimAddCardFlagVar.lean#L12-L20

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_DimAddCardFlagVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.FlagDim
open NumberField

theorem GlobalTheory.FlagDim.card_pairs_lt (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by sorry
