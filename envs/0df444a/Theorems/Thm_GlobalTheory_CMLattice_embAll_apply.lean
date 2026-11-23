-- Prove2me | Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- name    : GlobalTheory.CMLattice.embAll_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:25:51.280516+00:00
-- url     : https://prove2.me/theorems/dca489ae-190f-472c-944a-9693344fb398
-- title:
--   CMLattice: emb All apply
-- statement:
--   The CMLattice construction uses the emb All apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/EqTopOfForallEmbAllMem.lean#L78-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/EqTopOfForallEmbAllMem.lean#L78-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.CMLattice
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMLattice.embAll_apply (Ψ : Finset (E →+* ℂ)) (r : ℕ) (v : Fin r → E) (τ : Ψ) (a : Fin r) :
    embAll Ψ r v τ a = τ.1 (v a) := by sorry

attribute [defeq] GlobalTheory.CMLattice.embAll_apply
