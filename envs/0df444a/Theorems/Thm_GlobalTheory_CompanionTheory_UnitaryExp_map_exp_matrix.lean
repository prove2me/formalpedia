-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnitaryExp_map_exp_matrix
-- name    : GlobalTheory.CompanionTheory.UnitaryExp.map_exp_matrix
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:43.452279+00:00
-- url     : https://prove2.me/theorems/5aac5601-ee09-442b-af75-1cc0dff47a1d
-- title:
--   Unitary Exp: map exp matrix
-- statement:
--   The Unitary Exp construction uses the map exp matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/GlobalTheory/ExistsExpUnitary.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/GlobalTheory/ExistsExpUnitary.lean#L10-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ExistsExpEqOfMemKset
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_GlobalTheory_ExistsExpUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnitaryExp
open Matrix
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.CompanionTheory.UnitaryExp.map_exp_matrix {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (f : Matrix m m ℂ ≃ₐ[ℂ] Matrix n n ℂ) (hf : Continuous f) (S : Matrix m m ℂ) :
    f (NormedSpace.exp S) = NormedSpace.exp (f S) := by sorry
