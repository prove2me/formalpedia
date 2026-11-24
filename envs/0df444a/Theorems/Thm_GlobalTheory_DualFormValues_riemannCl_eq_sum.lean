-- Prove2me | Theorems.Thm_GlobalTheory_DualFormValues_riemannCl_eq_sum
-- name    : GlobalTheory.DualFormValues.riemannCl_eq_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:51:40.258799+00:00
-- url     : https://prove2.me/theorems/5ad09a49-6cbe-45d3-874e-8b8ba719c6ea
-- title:
--   Dual Form Values: riemann Cl eq sum
-- statement:
--   The Dual Form Values construction uses the riemann Cl eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RiemannClEqSum.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RiemannClEqSum.lean#L43-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RiemannClEqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DualFormValues
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]

theorem GlobalTheory.DualFormValues.riemannCl_eq_sum (ξ x : E) :
    riemannCl ξ x = ∑ σ : E →+* ℂ, σ (ξ * x) • (ComplexEmbedding.conjugate σ).toRatAlgHom.toLinearMap := by sorry
