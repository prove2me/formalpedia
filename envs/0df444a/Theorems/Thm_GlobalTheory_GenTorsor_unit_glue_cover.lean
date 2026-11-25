-- Prove2me | Theorems.Thm_GlobalTheory_GenTorsor_unit_glue_cover
-- name    : GlobalTheory.GenTorsor.unit_glue_cover
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:08.592702+00:00
-- url     : https://prove2.me/theorems/d8787f53-8df2-4299-a23d-8e446db90a77
-- title:
--   Gen Torsor: unit glue cover
-- statement:
--   The Gen Torsor construction uses the unit glue cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L112-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L112-L139

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
variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]

theorem GlobalTheory.GenTorsor.unit_glue_cover (hc : ∀ x : X, ∃ i y, a i y = x) (V : X.Opens)
    (u : ∀ i, Γ(T i, a i ⁻¹ᵁ V)ˣ)
    (h : ∀ i j (S : Scheme.{0}) (b : S ⟶ T i) (c : S ⟶ T j), b ≫ a i = c ≫ a j →
      ∀ (hb : ⊤ ≤ b ⁻¹ᵁ a i ⁻¹ᵁ V) (hc : ⊤ ≤ c ⁻¹ᵁ a j ⁻¹ᵁ V),
        pb b _ ⊤ hb (u i) = pb c _ ⊤ hc (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, pb (a i) V _ le_rfl s = u i := by sorry
