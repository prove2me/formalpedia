-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Witt_perp_perp
-- name    : GlobalTheory.Mass.Witt.perp_perp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:50.611802+00:00
-- url     : https://prove2.me/theorems/6eb3b971-ce24-5055-bfd1-deb08a85d2a4
-- title:
--   Witt: perp perp
-- statement:
--   The Witt construction uses the perp perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionTotallyDefiniteHermitian.lean#L111-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionTotallyDefiniteHermitian.lean#L111-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Witt
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem GlobalTheory.Mass.Witt.perp_perp [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x, h x x = 0 → x = 0) (U : Submodule K V) : perp h (perp h U) = U := by sorry
