-- Prove2me | Theorems.Thm_GlobalTheory_T_orbitStabilizerMass_prod_eq_mul
-- name    : GlobalTheory.T.orbitStabilizerMass_prod_eq_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:09:48.671503+00:00
-- url     : https://prove2.me/theorems/34da28fa-55a4-4eda-801e-3a44d7f3585c
-- title:
--   T: orbit Stabilizer Mass prod eq mul
-- statement:
--   The T construction uses the orbit Stabilizer Mass prod eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassProdEqMulStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassProdEqMulStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassProdEqMul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassProdEqMulStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.orbitStabilizerMass_prod_eq_mul : ∀ (Γ G G' α β : Type) [Group Γ] [Group G] [Group G'] [MulAction G α] [MulAction G' β] [MulAction Γ (α × β)] (φ : Γ ≃* G × G') (X : Set α) (Y : Set β), (∀ (γ : Γ) (p : α × β), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2)) → Stable G X → Stable G' Y → (∀ x ∈ X, Finite (MulAction.stabilizer G x)) → (∀ y ∈ Y, Finite (MulAction.stabilizer G' y)) → orbMass Γ (X ×ˢ Y) = orbMass G X * orbMass G' Y := by sorry
