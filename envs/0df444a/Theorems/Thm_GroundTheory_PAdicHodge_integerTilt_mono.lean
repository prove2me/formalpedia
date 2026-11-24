-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_integerTilt_mono
-- name    : GroundTheory.PAdicHodge.integerTilt_mono
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:05:21.202773+00:00
-- url     : https://prove2.me/theorems/bb25df93-a4b6-4ef3-8190-0552ab07257b
-- title:
--   PAdic Hodge: integer Tilt mono
-- statement:
--   The PAdic Hodge construction uses the integer Tilt mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltField.lean#L137-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltField.lean#L137-L139

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

theorem GroundTheory.PAdicHodge.integerTilt_mono {N N' : IntermediateField K♭ C♭} (h : N ≤ N') :
    integerTilt K C p N ≤ integerTilt K C p N' := by sorry
