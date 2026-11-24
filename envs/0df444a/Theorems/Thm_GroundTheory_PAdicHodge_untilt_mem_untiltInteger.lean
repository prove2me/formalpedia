-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_untilt_mem_untiltInteger
-- name    : GroundTheory.PAdicHodge.untilt_mem_untiltInteger
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:04:30.703798+00:00
-- url     : https://prove2.me/theorems/84cd304e-4baf-4a64-918c-049116837718
-- title:
--   PAdic Hodge: untilt mem untilt Integer
-- statement:
--   The PAdic Hodge construction uses the untilt mem untilt Integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltField.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltField.lean#L36-L40

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

theorem GroundTheory.PAdicHodge.untilt_mem_untiltInteger {N : IntermediateField K♭ C♭} {a : 𝒪C♭} (ha : a ∈ integerTilt K C p N) :
    PreTilt.untilt a ∈ untiltInteger K C p N := by sorry
