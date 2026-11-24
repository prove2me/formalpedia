-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_eq_zero_of_ode
-- name    : GroundTheory.Automorphic.ArchWhittaker.eq_zero_of_ode
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:31.631051+00:00
-- url     : https://prove2.me/theorems/ae0ff65d-23a3-43dd-92d5-4749a4d267f3
-- title:
--   Arch Whittaker: eq zero of ode
-- statement:
--   The Arch Whittaker construction uses the eq zero of ode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L283-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L283-L326

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_WronskianEqZeroOfModerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ArchWhittaker
open Filter Topology Set

theorem GroundTheory.Automorphic.ArchWhittaker.eq_zero_of_ode {q f f' : ℝ → ℂ} (hq : ContinuousOn q (Ioi 0))
    (hf : ∀ y > 0, HasDerivAt f (f' y) y) (hf' : ∀ y > 0, HasDerivAt f' (q y * f y) y)
    (h1 : f 1 = 0) (h1' : f' 1 = 0) : ∀ y > 0, f y = 0 := by sorry
