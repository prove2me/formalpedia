-- Prove2me | Theorems.Thm_GlobalTheory_SecAff_span_of_retract
-- name    : GlobalTheory.SecAff.span_of_retract
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:11.584823+00:00
-- url     : https://prove2.me/theorems/7966558e-f2ff-4896-a36f-4d36e2a0cc64
-- title:
--   Sec Aff: span of retract
-- statement:
--   The Sec Aff construction uses the span of retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L518-L526
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L518-L526

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
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}

theorem GlobalTheory.SecAff.span_of_retract (e : T'' ⟶ T') (e' : T' ⟶ T'') (he : e' ≫ e = 𝟙 T') (k : T'' ⟶ T)
    {κ : Type} (b : κ → SecM A L a T)
    (hb : Submodule.span Γ(T''.left, ⊤) (Set.range fun i => pull A L a k (b i)) = ⊤) :
    Submodule.span Γ(T'.left, ⊤) (Set.range fun i => pull A L a (e' ≫ k) (b i)) = ⊤ := by sorry
