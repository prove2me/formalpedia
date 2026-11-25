-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_NFUnique_exists_isometry
-- name    : GlobalTheory.DegAsm.NFUnique.exists_isometry
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:20:53.475621+00:00
-- url     : https://prove2.me/theorems/d34b65d4-c0b3-5b99-a72a-8bde5a16b998
-- title:
--   NFUnique: exists isometry
-- statement:
--   The NFUnique construction uses the exists isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormUniqueUpToUnipotent.lean#L30-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormUniqueUpToUnipotent.lean#L30-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormUniqueUpToUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.NFUnique
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem GlobalTheory.DegAsm.NFUnique.exists_isometry (S : Set (V × V)) (h : ∀ p ∈ S, ∀ q ∈ S, Cmp H p q)
    (h1 : (Submodule.span K S).map (LinearMap.fst K V V) = ⊤)
    (h2 : (Submodule.span K S).map (LinearMap.snd K V V) = ⊤) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, H.B (s x) (s y) = H.B x y) ∧ ∀ p ∈ S, s p.1 = p.2 := by sorry
