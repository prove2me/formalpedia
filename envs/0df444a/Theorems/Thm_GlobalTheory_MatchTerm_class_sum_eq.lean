-- Prove2me | Theorems.Thm_GlobalTheory_MatchTerm_class_sum_eq
-- name    : GlobalTheory.MatchTerm.class_sum_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:22:31.392934+00:00
-- url     : https://prove2.me/theorems/42c047a2-5045-41b5-bdc8-a4fe0d0b48f6
-- title:
--   Match Term: class sum eq
-- statement:
--   The Match Term construction uses the class sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaMatchingExistsRightTorusTorsion.lean#L34-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaMatchingExistsRightTorusTorsion.lean#L34-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Module Filter
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.MatchTerm
variable {K X X' : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X']

theorem GlobalTheory.MatchTerm.class_sum_eq [IsAlgClosed K] {M : ℕ} (hM : ‖(M : K)‖ = 1) (σ : X → K) (σ' : X' → K)
    (hσ : Tendsto σ cofinite (𝓝 0)) (hσ' : Tendsto σ' cofinite (𝓝 0)) (c : K) (α : X) (α' : X')
    (E : {t : Multiplicative X →* Kˣ // t ^ M = 1} → {t : Multiplicative X' →* Kˣ // t ^ M = 1})
    (hE : Function.Bijective E)
    (hα : ∀ t, (E t).1 (Multiplicative.ofAdd α') = t.1 (Multiplicative.ofAdd α))
    (hs : ∀ t, ∑' β, σ' β * ((E t).1 (Multiplicative.ofAdd β) : K) =
      c * ∑' β, σ β * (t.1 (Multiplicative.ofAdd β) : K)) :
    ∑' μ, σ' (α' + M • μ) = c * ∑' μ, σ (α + M • μ) := by sorry
