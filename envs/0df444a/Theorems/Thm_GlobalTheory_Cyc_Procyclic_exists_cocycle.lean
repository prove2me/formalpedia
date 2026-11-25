-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_Procyclic_exists_cocycle
-- name    : GlobalTheory.Cyc.Procyclic.exists_cocycle
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:26:23.384023+00:00
-- url     : https://prove2.me/theorems/231b58fe-fad3-57d8-8645-b7f8621f42be
-- title:
--   Procyclic: exists cocycle
-- statement:
--   The Procyclic construction uses the exists cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleVanishingOnFixingSubgroupDeterminedByGene.lean#L147-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleVanishingOnFixingSubgroupDeterminedByGene.lean#L147-L233

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

theorem GlobalTheory.Cyc.Procyclic.exists_cocycle [CompleteSpace X] [ContinuousMul Γ] {H : Subgroup Γ} (p : ℕ)
    (Gn : ℕ → Subgroup Γ) (hanti : Antitone Gn) (M : AddSubgroup X) (hMc : IsClosed (M : Set X))
    (hg : g ∈ G) (hw : w ∈ M) (hHG : H ≤ G) (hHn : ∀ n, H ≤ Gn n)
    (hnorm : ∀ σ ∈ G, ∀ h ∈ H, σ * h * σ⁻¹ ∈ H) (hone : ∀ y, A 1 y = y)
    (hmul : ∀ σ ∈ G, ∀ τ ∈ G, ∀ y, A (σ * τ) y = A σ (A τ y))
    (hn : ∀ σ ∈ G, ∀ y, ‖A σ y‖ ≤ ‖y‖) (hcont : ∀ y, ContinuousOn (fun σ => A σ y) G)
    (hAM : ∀ σ ∈ G, ∀ y ∈ M, A σ y ∈ M) (hHM : ∀ h ∈ H, ∀ y ∈ M, A h y = y)
    (hopen : ∀ N, ∀ σ ∈ G, ∀ᶠ τ in 𝓝[G] σ, τ * σ⁻¹ ∈ Gn N)
    (hcos : ∀ σ ∈ G, ∀ n, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gn n)
    (hd : (G : Set Γ) ⊆ closure {x | ∃ h ∈ H, ∃ a : ℕ, x = h * g ^ a})
    (hdvd : ∀ k, ∃ N, ∀ d : ℕ, g ^ d ∈ Gn N → p ^ k ∣ d)
    (hD : ∀ ε > 0, ∃ k : ℕ, ‖A (g ^ p ^ k) w - w‖ ≤ ε)
    (hp : ∀ ε > 0, ∃ s : ℕ, ∀ y : X, ‖y‖ ≤ ‖w‖ → ‖p ^ s • y‖ ≤ ε) :
    ∃ c : Γ → X, ContinuousOn c G ∧ (∀ σ ∈ G, c σ ∈ M) ∧
      (∀ σ ∈ G, ∀ τ ∈ G, c (σ * τ) = c σ + A σ (c τ)) ∧ (∀ h ∈ H, c h = 0) ∧ c g = w := by sorry
