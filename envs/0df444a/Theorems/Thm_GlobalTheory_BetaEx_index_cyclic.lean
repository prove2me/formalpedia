-- Prove2me | Theorems.Thm_GlobalTheory_BetaEx_index_cyclic
-- name    : GlobalTheory.BetaEx.index_cyclic
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:13.453572+00:00
-- url     : https://prove2.me/theorems/c07bf007-a94b-43a4-bff0-ce4331e8ca71
-- title:
--   Beta Ex: index cyclic
-- statement:
--   The Beta Ex construction uses the index cyclic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L177-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L177-L182

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
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem GlobalTheory.BetaEx.index_cyclic (M' : Submodule (𝓞 E) (Fin n → E)) (m : Fin n → E) :
    Ideal.absNorm (M'.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) =
      M'.toAddSubgroup.relIndex (M' ⊔ Submodule.span (𝓞 E) {m}).toAddSubgroup := by sorry
