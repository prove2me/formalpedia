-- Prove2me | Theorems.Thm_GlobalTheory_Mass_DiscOrder_exists_max_of_covBy
-- name    : GlobalTheory.Mass.DiscOrder.exists_max_of_covBy
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:58.613403+00:00
-- url     : https://prove2.me/theorems/45dd2c8d-871b-42e1-b570-fdc651d11c69
-- title:
--   Disc Order: exists max of cov By
-- statement:
--   The Disc Order construction uses the exists max of cov By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianLatticeDiscriminantOrderNeZeroUnimodula.lean#L29-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianLatticeDiscriminantOrderNeZeroUnimodula.lean#L29-L47

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
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem GlobalTheory.Mass.DiscOrder.exists_max_of_covBy {X Y : Submodule R W} (h : X ⋖ Y) :
    ∃ P : Ideal R, P.IsMaximal ∧ (∀ r : R, r ∈ P ↔ ∀ y ∈ Y, r • y ∈ X) ∧ idxN Y X = Nat.card (R ⧸ P) := by sorry
