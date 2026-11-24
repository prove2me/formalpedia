-- Prove2me | Theorems.Thm_GlobalTheory_AbelianQuotient_exists_grpObj
-- name    : GlobalTheory.AbelianQuotient.exists_grpObj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:52:14.284593+00:00
-- url     : https://prove2.me/theorems/ccb64f63-112f-4b6c-a718-2bf668323983
-- title:
--   Abelian Quotient: exists grp Obj
-- statement:
--   The Abelian Quotient construction uses the exists grp Obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuotientIsAbelianSchemeOfQuotientScheme.lean#L50-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuotientIsAbelianSchemeOfQuotientScheme.lean#L50-L153

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme
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
open GlobalTheory
open GlobalTheory.AbelianQuotient
variable {S : Scheme.{0}}

theorem GlobalTheory.AbelianQuotient.exists_grpObj {A H Q : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj H] (i : H ⟶ A)
    [IsMonHom i] (q : A ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hq : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q) :
    ∃ _ : GrpObj Q, IsCommMonObj Q ∧ IsMonHom q ∧ IsPullback i (toUnit H) q η[Q] := by sorry
