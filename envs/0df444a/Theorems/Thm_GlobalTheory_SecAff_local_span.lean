-- Prove2me | Theorems.Thm_GlobalTheory_SecAff_local_span
-- name    : GlobalTheory.SecAff.local_span
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:48:07.178805+00:00
-- url     : https://prove2.me/theorems/23a5ce64-0a9d-4241-8c65-849a891e4921
-- title:
--   Sec Aff: local span
-- statement:
--   The Sec Aff construction uses the local span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L549-L559
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L549-L559

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff

theorem GlobalTheory.SecAff.local_span (H : SecBaseChangeSt) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S)
    (n : ℕ) (hn : 1 ≤ n) (p : S) : ∃ V : S.Opens, p ∈ V ∧
      ∃ b : Fin (n ^ P.g) → SecM P.A P.L n (overRes (T := baseOver S) V),
        ∀ (T' : Over S) [IsAffine T'.left] (g : T' ⟶ overRes (T := baseOver S) V),
          Submodule.span Γ(T'.left, ⊤) (Set.range fun i => pull P.A P.L n g (b i)) = ⊤ := by sorry
