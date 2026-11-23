-- Prove2me | Theorems.Thm_GroundTheory_Global_natCard_residueField_adicCompletionIntegers
-- name    : GroundTheory.Global.natCard_residueField_adicCompletionIntegers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:51.045689+00:00
-- url     : https://prove2.me/theorems/8231aaa2-f180-4309-b12a-839bd380674f
-- title:
--   Global: nat Card residue Field adic Completion Integers
-- statement:
--   The Global construction uses the nat Card residue Field adic Completion Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalAtPlace.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalAtPlace.lean#L92-L96

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open GroundTheory GroundTheory.Global
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Global.natCard_residueField_adicCompletionIntegers :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) =
      Ideal.absNorm v.asIdeal := by sorry
