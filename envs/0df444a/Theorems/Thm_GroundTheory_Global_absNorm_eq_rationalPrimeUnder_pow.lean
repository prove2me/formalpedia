-- Prove2me | Theorems.Thm_GroundTheory_Global_absNorm_eq_rationalPrimeUnder_pow
-- name    : GroundTheory.Global.absNorm_eq_rationalPrimeUnder_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:05.822515+00:00
-- url     : https://prove2.me/theorems/4f7e4506-0d81-4738-a8a8-f37d03ca52fb
-- title:
--   Global: abs Norm eq rational Prime Under pow
-- statement:
--   The Global construction uses the abs Norm eq rational Prime Under pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L41-L43

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

theorem GroundTheory.Global.absNorm_eq_rationalPrimeUnder_pow (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm w.asIdeal = rationalPrimeUnder w ^ w.asIdeal.inertiaDeg ℤ := by sorry
