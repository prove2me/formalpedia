-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_Procyclic_eqOn_of_dense
-- name    : GlobalTheory.Cyc.Procyclic.eqOn_of_dense
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:10:21.442818+00:00
-- url     : https://prove2.me/theorems/dacc70b4-254f-4226-8e76-bd708d73eb70
-- title:
--   Procyclic: eq On of dense
-- statement:
--   The Procyclic construction uses the eq On of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleVanishingOnFixingSubgroupDeterminedByGene.lean#L110-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleVanishingOnFixingSubgroupDeterminedByGene.lean#L110-L118

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
variable [TopologicalSpace Γ]
omit [IsUltrametricDist X]

theorem GlobalTheory.Cyc.Procyclic.eqOn_of_dense {H : Subgroup Γ} (hg : g ∈ G) (hHG : H ≤ G)
    (hd : (G : Set Γ) ⊆ closure {x | ∃ h ∈ H, ∃ a : ℕ, x = h * g ^ a}) {f₁ f₂ : Γ → X}
    (h₁ : ContinuousOn f₁ G) (h₂ : ContinuousOn f₂ G)
    (h : ∀ h ∈ H, ∀ a : ℕ, f₁ (h * g ^ a) = f₂ (h * g ^ a)) : ∀ σ ∈ G, f₁ σ = f₂ σ := by sorry
