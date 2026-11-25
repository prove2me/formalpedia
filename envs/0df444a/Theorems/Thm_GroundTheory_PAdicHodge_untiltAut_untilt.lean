-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_untiltAut_untilt
-- name    : GroundTheory.PAdicHodge.untiltAut_untilt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:00:46.641475+00:00
-- url     : https://prove2.me/theorems/5c9fd3ca-3742-4c12-9bdf-8ceaf70f540f
-- title:
--   PAdic Hodge: untilt Aut untilt
-- statement:
--   The PAdic Hodge construction uses the untilt Aut untilt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGalois.lean#L373-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGalois.lean#L373-L379

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
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

theorem GroundTheory.PAdicHodge.untiltAut_untilt (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] (σ : N ≃ₐ[K♭] N)
    (b : PreTilt (normInteger (untiltField K C p N)) p) :
    untiltAut N σ ((PreTilt.untilt b : normInteger (untiltField K C p N)) : untiltField K C p N) =
      ((PreTilt.untilt (untiltPreTiltAut N σ b) : normInteger (untiltField K C p N)) :
        untiltField K C p N) := by sorry
