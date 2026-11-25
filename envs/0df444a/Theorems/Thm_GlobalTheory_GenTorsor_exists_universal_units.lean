-- Prove2me | Theorems.Thm_GlobalTheory_GenTorsor_exists_universal_units
-- name    : GlobalTheory.GenTorsor.exists_universal_units
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:01.845566+00:00
-- url     : https://prove2.me/theorems/25371bc5-930d-48d8-a2f4-2694699a2679
-- title:
--   Gen Torsor: exists universal units
-- statement:
--   The Gen Torsor construction uses the exists universal units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L143-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L143-L189

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenTorsor
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.GenTorsor.exists_universal_units (K : Type) :
    ∃ (T : Scheme.{0}) (e : K → Γ(T, ⊤)ˣ), ∀ (Z : Scheme.{0}) (u : K → Γ(Z, ⊤)ˣ),
      ∃! c : Z ⟶ T, ∀ k, pb c ⊤ ⊤ le_rfl (e k) = u k := by sorry
