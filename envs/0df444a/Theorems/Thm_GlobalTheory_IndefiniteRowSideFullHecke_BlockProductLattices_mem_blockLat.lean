-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_BlockProductLattices_mem_blockLat
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.mem_blockLat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:14:46.861163+00:00
-- url     : https://prove2.me/theorems/b20bb7eb-b32a-43c6-b7c1-cefe92e2624f
-- title:
--   Block Product Lattices: mem block Lat
-- statement:
--   The Block Product Lattices construction uses the mem block Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/BlockProductLattices.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/BlockProductLattices.lean#L22-L24

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices
open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] {n₁ n₂ : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.mem_blockLat (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (v : Fin (n₁ + n₂) → E) :
    v ∈ (blockLat Λ₁ Λ₂).La ↔
      (fun j => v (Fin.castAdd n₂ j)) ∈ Λ₁.La ∧ (fun j => v (Fin.natAdd n₁ j)) ∈ Λ₂.La := by sorry
