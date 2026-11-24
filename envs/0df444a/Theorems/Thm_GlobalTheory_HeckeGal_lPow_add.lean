-- Prove2me | Theorems.Thm_GlobalTheory_HeckeGal_lPow_add
-- name    : GlobalTheory.HeckeGal.lPow_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:54.542807+00:00
-- url     : https://prove2.me/theorems/904fb60b-f18a-4971-8ab3-85237401ec57
-- title:
--   Hecke Gal: l Pow add
-- statement:
--   The Hecke Gal construction uses the l Pow add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L221-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L221-L226

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

theorem GlobalTheory.HeckeGal.lPow_add (ι : Qbar l ≃+* ℂ) (n n' : (E →+* ℂ) → ℤ) (x : Ideles E) :
    lPow ι (n + n') x = lPow ι n x * lPow ι n' x := by sorry
