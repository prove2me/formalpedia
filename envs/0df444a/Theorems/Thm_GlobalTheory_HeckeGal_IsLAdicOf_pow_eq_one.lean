-- Prove2me | Theorems.Thm_GlobalTheory_HeckeGal_IsLAdicOf_pow_eq_one
-- name    : GlobalTheory.HeckeGal.IsLAdicOf.pow_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:36.405553+00:00
-- url     : https://prove2.me/theorems/8efe4dfe-c540-4273-81e0-5dcf9333423f
-- title:
--   Is LAdic Of: pow eq one
-- statement:
--   The Is LAdic Of construction uses the pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L446-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L446-L454

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory GlobalTheory.HeckeGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.HeckeGal.IsLAdicOf.pow_eq_one {art : Ideles E →* Gab E Ω} (hs : Function.Surjective art) {ι : Qbar l ≃+* ℂ}
    {χ : HChar E} {r : G E Ω →* (Qbar l)ˣ} (h : IsLAdicOf art ι χ 0 r) {m : ℕ} (hχ : χ.OrderDvd m) :
    r ^ m = 1 := by sorry
