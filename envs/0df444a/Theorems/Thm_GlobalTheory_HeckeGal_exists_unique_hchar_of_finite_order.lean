-- Prove2me | Theorems.Thm_GlobalTheory_HeckeGal_exists_unique_hchar_of_finite_order
-- name    : GlobalTheory.HeckeGal.exists_unique_hchar_of_finite_order
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:03:02.831705+00:00
-- url     : https://prove2.me/theorems/3e9fdeb4-5706-43e3-b325-5fb84725fe19
-- title:
--   Hecke Gal: exists unique hchar of finite order
-- statement:
--   The Hecke Gal construction uses the exists unique hchar of finite order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L381-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L381-L418

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

theorem GlobalTheory.HeckeGal.exists_unique_hchar_of_finite_order {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* (Qbar l)ˣ) (hr : Continuous r) {m : ℕ} (hm : 0 < m) (h : r ^ m = 1) :
    ∃! χ : HChar E, χ.OrderDvd m ∧ IsLAdicOf art ι χ 0 r := by sorry
