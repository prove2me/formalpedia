-- Prove2me | Theorems.Thm_GlobalTheory_HeckeGal_isAlgPos_zero_of_orderDvd
-- name    : GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:29.563109+00:00
-- url     : https://prove2.me/theorems/d3cf7210-7482-4548-9080-d8425a3ec56e
-- title:
--   Hecke Gal: is Alg Pos zero of order Dvd
-- statement:
--   The Hecke Gal construction uses the is Alg Pos zero of order Dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L420-L444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L420-L444

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

theorem GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd {χ : HChar E} {m : ℕ} (hm : 0 < m) (h : χ.OrderDvd m) : IsAlgPos χ 0 := by sorry
