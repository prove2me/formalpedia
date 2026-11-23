-- Prove2me | Theorems.Thm_GlobalTheory_AdeleDiscrete_exists_nhds_zero_principal_eq_zero
-- name    : GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:15.499452+00:00
-- url     : https://prove2.me/theorems/3ac1f4ab-0101-4824-bb0c-768ddd3cbddd
-- title:
--   Adele Discrete: exists nhds zero principal eq zero
-- statement:
--   The Adele Discrete construction uses the exists nhds zero principal eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsNhdsZeroPrincipalEqZero.lean#L7-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsNhdsZeroPrincipalEqZero.lean#L7-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsNhdsZeroPrincipalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory GlobalTheory.AdeleDiscrete

theorem GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero : ∀ (F : Type) [Field F] [NumberField F], ∃ U ∈ nhds (0 : AdeleRing (𝓞 F) F), ∀ x : F, algebraMap F (AdeleRing (𝓞 F) F) x ∈ U → x = 0 := by sorry
