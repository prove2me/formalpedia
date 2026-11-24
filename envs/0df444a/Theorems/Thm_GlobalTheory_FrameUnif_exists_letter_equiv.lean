-- Prove2me | Theorems.Thm_GlobalTheory_FrameUnif_exists_letter_equiv
-- name    : GlobalTheory.FrameUnif.exists_letter_equiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:36:01.226366+00:00
-- url     : https://prove2.me/theorems/ee00b84e-aec9-4589-ad98-ff85108f1516
-- title:
--   Frame Unif: exists letter equiv
-- statement:
--   The Frame Unif construction uses the exists letter equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmTypeLetterFrameColumnDictionary.lean#L18-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmTypeLetterFrameColumnDictionary.lean#L18-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RelabelEmbeddingsGoodBijectiveConjCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmTypeLetterFrameColumnDictionary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.FrameUnif

theorem GlobalTheory.FrameUnif.exists_letter_equiv {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (p q r : ℕ) (hr : r = p + q)
    (ρ : (E →+* ℂ) → (E →+* ℂ)) (hρ : Function.Bijective ρ) (m : (E →+* ℂ) → ℕ)
    (hp : ∀ τ, ρ τ ∈ Ψ → m τ = p) (hq : ∀ τ, ρ τ ∉ Ψ → m τ = q) :
    ∃ f : (Σ τ, Fin (m τ)) ≃ Ψ × Fin r, ∀ s,
      (ρ s.1 ∈ Ψ ∧ (f s).1.1 = ρ s.1 ∧ ((f s).2 : ℕ) = q + s.2) ∨
      (ρ s.1 ∉ Ψ ∧ (f s).1.1 = ComplexEmbedding.conjugate (ρ s.1) ∧ ((f s).2 : ℕ) = q - 1 - s.2 ∧ (s.2 : ℕ) < q) := by sorry
