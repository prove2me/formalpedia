-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_Procyclic_exists_norm_psum_sub_le
-- name    : GlobalTheory.Cyc.Procyclic.exists_norm_psum_sub_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:20:28.521623+00:00
-- url     : https://prove2.me/theorems/b3758aa0-53f2-5a12-9b1b-9f37253384d1
-- title:
--   Procyclic: exists norm psum sub le
-- statement:
--   The Procyclic construction uses the exists norm psum sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleVanishingOnFixingSubgroupDeterminedByGene.lean#L86-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleVanishingOnFixingSubgroupDeterminedByGene.lean#L86-L105

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Filter Topology
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Procyclic
variable {Γ X : Type} [Group Γ] [NormedAddCommGroup X]
variable {G : Subgroup Γ} {A : Γ → X →+ X} {g : Γ} {w : X}
variable [IsUltrametricDist X]

theorem GlobalTheory.Cyc.Procyclic.exists_norm_psum_sub_le (p : ℕ) (hg : g ∈ G) (hone : ∀ y, A 1 y = y)
    (hmul : ∀ σ ∈ G, ∀ τ ∈ G, ∀ y, A (σ * τ) y = A σ (A τ y))
    (hn : ∀ σ ∈ G, ∀ y, ‖A σ y‖ ≤ ‖y‖)
    (hD : ∀ ε > 0, ∃ k : ℕ, ‖A (g ^ p ^ k) w - w‖ ≤ ε)
    (hp : ∀ ε > 0, ∃ s : ℕ, ∀ y : X, ‖y‖ ≤ ‖w‖ → ‖p ^ s • y‖ ≤ ε) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ a d : ℕ, p ^ k ∣ d → ‖psum A g w (a + d) - psum A g w a‖ ≤ ε := by sorry
