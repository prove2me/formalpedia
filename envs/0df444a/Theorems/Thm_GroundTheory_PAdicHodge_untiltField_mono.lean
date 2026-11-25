-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_untiltField_mono
-- name    : GroundTheory.PAdicHodge.untiltField_mono
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:04:13.478579+00:00
-- url     : https://prove2.me/theorems/702f205c-6295-404f-b93f-abc59e60b1db
-- title:
--   PAdic Hodge: untilt Field mono
-- statement:
--   The PAdic Hodge construction uses the untilt Field mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltField.lean#L148-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltField.lean#L148-L150

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
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
local notation "𝒪C♭" => PreTilt (normInteger C) p
local notation "θ" => WittVector.fontaineTheta (normInteger C) p

theorem GroundTheory.PAdicHodge.untiltField_mono {N N' : IntermediateField K♭ C♭} (h : N ≤ N') :
    untiltField K C p N ≤ untiltField K C p N' := by sorry
