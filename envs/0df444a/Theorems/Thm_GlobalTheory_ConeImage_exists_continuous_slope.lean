-- Prove2me | Theorems.Thm_GlobalTheory_ConeImage_exists_continuous_slope
-- name    : GlobalTheory.ConeImage.exists_continuous_slope
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:25:38.466959+00:00
-- url     : https://prove2.me/theorems/268905d0-fed2-4f46-95be-d2495c5e53cd
-- title:
--   Cone Image: exists continuous slope
-- statement:
--   The Cone Image construction uses the exists continuous slope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsNhdsSubsetRange.lean#L85-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsNhdsSubsetRange.lean#L85-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ConeImage

theorem GlobalTheory.ConeImage.exists_continuous_slope {σ : Type*} (p : Polynomial (MvPolynomial σ ℂ)) :
    ∃ k : (σ → ℂ) × ℂ × ℂ → ℂ, Continuous k ∧ ∀ u s s',
      p.eval₂ (MvPolynomial.eval u) s' - p.eval₂ (MvPolynomial.eval u) s
        = (s' - s) * k (u, s, s') ∧
      k (u, s, s) = p.derivative.eval₂ (MvPolynomial.eval u) s := by sorry
