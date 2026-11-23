-- Prove2me | Theorems.Thm_GlobalTheory_length_localizedModule_eq_add_of_exact
-- name    : GlobalTheory.length_localizedModule_eq_add_of_exact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:55.001499+00:00
-- url     : https://prove2.me/theorems/0239a4ae-a458-4c9a-b57c-13cbf8c53865
-- title:
--   Global Theory: length localized Module eq add of exact
-- statement:
--   The Global Theory construction uses the length localized Module eq add of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L52-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L52-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {S : Type*} [CommRing S]

theorem GlobalTheory.length_localizedModule_eq_add_of_exact (T : Submonoid S) {N M P : Type*}
    [AddCommGroup N] [AddCommGroup M] [AddCommGroup P] [Module S N] [Module S M] [Module S P]
    (f : N →ₗ[S] M) (g : M →ₗ[S] P) (hf : Function.Injective f) (hg : Function.Surjective g)
    (H : Function.Exact f g) :
    Module.length (Localization T) (LocalizedModule T M) =
      Module.length (Localization T) (LocalizedModule T N) +
        Module.length (Localization T) (LocalizedModule T P) := by sorry
