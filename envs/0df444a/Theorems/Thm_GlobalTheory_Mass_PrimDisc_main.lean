-- Prove2me | Theorems.Thm_GlobalTheory_Mass_PrimDisc_main
-- name    : GlobalTheory.Mass.PrimDisc.main
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:39:18.252704+00:00
-- url     : https://prove2.me/theorems/b8900c52-084b-5e4d-abf4-0070839766b0
-- title:
--   Prim Disc: main
-- statement:
--   The Prim Disc construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveHermitianSublatticeDiscriminantGenerato.lean#L150-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveHermitianSublatticeDiscriminantGenerato.lean#L150-L190

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveHermitianSublatticeDiscriminantGenerato
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_main

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.PrimDisc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.Mass.PrimDisc.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (L : Submodule (𝓞 K) V) (U : Submodule K V) (e : ℕ), IsIntLat h L → (∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) → IsIntLat (hRes h U) (latIn U L) ∧ IsIntLat (hRes h (perp h U)) (latIn (perp h U) L) ∧ discN (hRes h (perp h U)) (latIn (perp h U) L) ≤ discN (hRes h U) (latIn U L) * discN h L ∧ (∃ t : Finset ↥U, t.card ≤ (Module.finrank K (perp h U) + e) ∧ dual (hRes h U) (latIn U L) = (latIn U L) ⊔ Submodule.span (𝓞 K) (t : Set _)) := by sorry
