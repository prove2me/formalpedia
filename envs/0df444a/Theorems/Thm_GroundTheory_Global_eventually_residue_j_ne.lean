-- Prove2me | Theorems.Thm_GroundTheory_Global_eventually_residue_j_ne
-- name    : GroundTheory.Global.eventually_residue_j_ne
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:40:48.309647+00:00
-- url     : https://prove2.me/theorems/1161a16a-40d6-4c09-b2ed-a597384e005f
-- title:
--   Global: eventually residue j ne
-- statement:
--   The Global construction uses the eventually residue j ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/GoodReductionAlmostAll.lean#L46-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/GoodReductionAlmostAll.lean#L46-L59

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
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
open NumberField IsDedekindDomain IsLocalRing
noncomputable section
variable {L : Type*} [Field L] [NumberField L]

theorem GroundTheory.Global.eventually_residue_j_ne {E E' : WeierstrassCurve L} [E.IsElliptic] [E'.IsElliptic]
    (hj : E.j ≠ E'.j) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∀ (W W' : WeierstrassCurve (localizationAt L v)) [W.IsElliptic] [W'.IsElliptic],
        W.map (algebraMap (localizationAt L v) L) = E →
          W'.map (algebraMap (localizationAt L v) L) = E' →
            residue (localizationAt L v) W.j ≠ residue (localizationAt L v) W'.j := by sorry
