-- Prove2me | Theorems.Thm_GroundTheory_Global_under_int_ne_bot
-- name    : GroundTheory.Global.under_int_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:40.979284+00:00
-- url     : https://prove2.me/theorems/c3d22387-800c-4e8b-85bb-dadeca0705fa
-- title:
--   Global: under int ne bot
-- statement:
--   The Global construction uses the under int ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L27-L28

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set
noncomputable section
variable {K L : Type*} [Field L] [NumberField L]
omit [NumberField L]

theorem GroundTheory.Global.under_int_ne_bot (w : HeightOneSpectrum (𝓞 L)) : w.asIdeal.under ℤ ≠ ⊥ := by sorry
