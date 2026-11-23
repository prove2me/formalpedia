-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_dens_opU
-- name    : GlobalTheory.ThetaInter.dens_opU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:44.054492+00:00
-- url     : https://prove2.me/theorems/38a65284-b1cd-4d09-a546-108e11fbcbcd
-- title:
--   Theta Inter: dens op U
-- statement:
--   The Theta Inter construction uses the dens op U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L264-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L264-L272

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
variable {α : V → ℂ}

theorem GlobalTheory.ThetaInter.dens_opU (hH : IsHerm H) (x : V) (F G : V → ℂ) (z : V) :
    dens H (opU H x F) (opU H x G) z = dens H F G (z + x) := by sorry
