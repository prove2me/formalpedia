-- Prove2me | Theorems.Thm_GlobalTheory_Mass_ProdMass_wt_prod
-- name    : GlobalTheory.Mass.ProdMass.wt_prod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:53.40768+00:00
-- url     : https://prove2.me/theorems/062fbf88-dc8a-42ac-aebf-b7053c15bc99
-- title:
--   Prod Mass: wt prod
-- statement:
--   The Prod Mass construction uses the wt prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassProdEqMul.lean#L73-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassProdEqMul.lean#L73-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassProdEqMul
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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.ProdMass
variable {Γ G G' α β : Type} [Group Γ] [Group G] [Group G'] [MulAction G α] [MulAction G' β]
  [MulAction Γ (α × β)] (φ : Γ ≃* G × G')
  (hφ : ∀ (γ : Γ) (p : α × β), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2))
include hφ

theorem GlobalTheory.Mass.ProdMass.wt_prod (X : Set α) (Y : Set β) (p : α × β) :
    wt Γ (X ×ˢ Y) p = wt G X p.1 * wt G' Y p.2 := by sorry
