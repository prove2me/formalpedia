-- Prove2me | Theorems.Thm_GroundTheory_Global_eventually_goodReduction
-- name    : GroundTheory.Global.eventually_goodReduction
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:55:24.731103+00:00
-- url     : https://prove2.me/theorems/8513116c-9c6b-5fa8-a5b2-150e513f9e5c
-- title:
--   Global: eventually good Reduction
-- statement:
--   The Global construction uses the eventually good Reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/GoodReductionAlmostAll.lean#L65-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/GoodReductionAlmostAll.lean#L65-L86

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

theorem GroundTheory.Global.eventually_goodReduction {ι : Type*} [Finite ι] (E : ι → WeierstrassCurve L)
    [∀ i, (E i).IsElliptic] (hE : Pairwise fun i k => (E i).j ≠ (E k).j) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ (W : ι → WeierstrassCurve (localizationAt L v)) (_ : ∀ i, (W i).IsElliptic),
        (∀ i, (W i).map (algebraMap (localizationAt L v) L) = E i) ∧
        (∀ i, algebraMap (localizationAt L v) L (W i).j = (E i).j) ∧
        Pairwise fun i k => residue (localizationAt L v) (W i).j ≠
          residue (localizationAt L v) (W k).j := by sorry
