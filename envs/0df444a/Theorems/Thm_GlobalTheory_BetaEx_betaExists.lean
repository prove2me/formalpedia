-- Prove2me | Theorems.Thm_GlobalTheory_BetaEx_betaExists
-- name    : GlobalTheory.BetaEx.betaExists
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:24.957821+00:00
-- url     : https://prove2.me/theorems/9d30c9d3-fefa-47ae-a0b4-6bd7c03951ee
-- title:
--   Beta Ex: beta Exists
-- statement:
--   The Beta Ex construction uses the beta Exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L322-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L322-L341

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem GlobalTheory.BetaEx.betaExists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (n bad : ℕ), Formalism.L2.Pj.BetaExists (Dw := Dw) c n bad := by sorry
