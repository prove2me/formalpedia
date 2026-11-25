-- Prove2me | Theorems.Thm_GlobalTheory_CuspFlow_exists_linear
-- name    : GlobalTheory.CuspFlow.exists_linear
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:40:53.62974+00:00
-- url     : https://prove2.me/theorems/8ef2c60f-8196-41d8-a140-bfa2f26d414e
-- title:
--   Cusp Flow: exists linear
-- statement:
--   The Cusp Flow construction uses the exists linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CuspFlowEqTorusAction.lean#L56-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CuspFlowEqTorusAction.lean#L56-L123

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

theorem GlobalTheory.CuspFlow.exists_linear (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (η : Fin ρ → E) (hη : (∑ a, η a • cu.e a) ∈ X.Λ) :
    ∃ L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ),
      (∀ (s : X.Ψ → ℝ) (τ : X.Ψ) (a b : Fin ρ), ∑ k, (L s k : ℂ) * τ.1 (zBas X cu k a b) =
        τ.1 X.κ0 * (s τ : ℂ) * (τ.1 (η a) * conj (τ.1 (η b)))) ∧
      ∀ (la : Wt X.Ψ r), ∀ p ∈ X.periods la, ∀ k, ∃ z : ℤ, L p k = z := by sorry
