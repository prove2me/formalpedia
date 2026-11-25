-- Prove2me | Theorems.Thm_GlobalTheory_CuspFlow_exists_int_coords
-- name    : GlobalTheory.CuspFlow.exists_int_coords
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:40:45.215674+00:00
-- url     : https://prove2.me/theorems/2bd5fe22-2208-42f7-8288-cd05fa2b9af0
-- title:
--   Cusp Flow: exists int coords
-- statement:
--   The Cusp Flow construction uses the exists int coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CuspFlowEqTorusAction.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CuspFlowEqTorusAction.lean#L42-L54

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsSt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CuspFlowEqTorusAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CuspFlow
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem GlobalTheory.CuspFlow.exists_int_coords (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (η : Fin ρ → E) (hη : (∑ a, η a • cu.e a) ∈ X.Λ) (a : E) (ha : cc a = a)
    (hai : IsIntegral ℤ a) :
    ∃ c : Fin (nZ X ρ) → ℤ, ∑ k, c k • zBas X cu k = ((X.m : E) * a * X.κ0) • mcMη η := by sorry
