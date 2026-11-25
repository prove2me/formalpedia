-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_untiltField_eq_of_le
-- name    : GroundTheory.PAdicHodge.exists_untiltField_eq_of_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:08:58.543019+00:00
-- url     : https://prove2.me/theorems/9ab450b0-6c02-4ae3-b0a7-5dc87e9648b9
-- title:
--   PAdic Hodge: exists untilt Field eq of le
-- statement:
--   The PAdic Hodge construction uses the exists untilt Field eq of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean#L149-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean#L149-L239

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem GroundTheory.PAdicHodge.exists_untiltField_eq_of_le (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [IsGalois K♭ N] (L : IntermediateField K C) (hL : L ≤ untiltField K C p N) :
    ∃ M : IntermediateField K♭ C♭, M ≤ N ∧ FiniteDimensional K♭ M ∧ untiltField K C p M = L := by sorry
