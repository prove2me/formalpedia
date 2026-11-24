-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_monic_monicOfCoeffs
-- name    : GroundTheory.PAdicHodge.monic_monicOfCoeffs
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:04:44.23443+00:00
-- url     : https://prove2.me/theorems/136234f6-1e98-488b-8891-d096f7d37386
-- title:
--   PAdic Hodge: monic monic Of Coeffs
-- statement:
--   The PAdic Hodge construction uses the monic monic Of Coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L160-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L160-L165

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
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
open Polynomial
variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField C p]
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem GroundTheory.PAdicHodge.monic_monicOfCoeffs (e : ℕ) (a : ℕ → 𝒪C♭) : (monicOfCoeffs e a).Monic := by sorry
