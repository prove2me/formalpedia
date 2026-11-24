-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_natDegree_monicOfCoeffs
-- name    : GroundTheory.PAdicHodge.natDegree_monicOfCoeffs
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:46.121607+00:00
-- url     : https://prove2.me/theorems/12c5ed33-2457-46c0-9d4c-301f22bb7bcb
-- title:
--   PAdic Hodge: nat Degree monic Of Coeffs
-- statement:
--   The PAdic Hodge construction uses the nat Degree monic Of Coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L178-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L178-L188

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

theorem GroundTheory.PAdicHodge.natDegree_monicOfCoeffs (e : ℕ) (a : ℕ → 𝒪C♭) : (monicOfCoeffs e a).natDegree = e := by sorry
