-- Prove2me | Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_dual
-- name    : GlobalTheory.Mass.DiscOrder.idxN_dual
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:32:22.748888+00:00
-- url     : https://prove2.me/theorems/7510d119-5cdd-4ac4-9a6d-544ba89ae35a
-- title:
--   Disc Order: idx N dual
-- statement:
--   The Disc Order construction uses the idx N dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianLatticeDiscriminantOrderNeZeroUnimodula.lean#L133-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianLatticeDiscriminantOrderNeZeroUnimodula.lean#L133-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hs hn

theorem GlobalTheory.Mass.DiscOrder.idxN_dual {X : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X) : ∀ (n : ℕ)
    (Y : Submodule (𝓞 K) V), Submodule.IsLattice K Y → X ≤ Y → idxN Y X = n →
    idxN (dual h X) (dual h Y) = n := by sorry
