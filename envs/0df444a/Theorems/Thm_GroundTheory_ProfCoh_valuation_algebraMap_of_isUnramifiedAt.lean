-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_valuation_algebraMap_of_isUnramifiedAt
-- name    : GroundTheory.ProfCoh.valuation_algebraMap_of_isUnramifiedAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:46.424931+00:00
-- url     : https://prove2.me/theorems/43f0cdde-5f4c-4456-bdea-73c7b718016d
-- title:
--   Prof Coh: valuation algebra Map of is Unramified At
-- statement:
--   The Prof Coh construction uses the valuation algebra Map of is Unramified At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ValuationTransport.lean#L80-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ValuationTransport.lean#L80-L87

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ValuationTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem GroundTheory.ProfCoh.valuation_algebraMap_of_isUnramifiedAt (w : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 L)) [W.asIdeal.LiesOver w.asIdeal]
    [Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal] (x : K) :
    W.valuation L (algebraMap K L x) = w.valuation K x := by sorry
