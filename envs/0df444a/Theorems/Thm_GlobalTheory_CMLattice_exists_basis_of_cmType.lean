-- Prove2me | Theorems.Thm_GlobalTheory_CMLattice_exists_basis_of_cmType
-- name    : GlobalTheory.CMLattice.exists_basis_of_cmType
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:32:36.671743+00:00
-- url     : https://prove2.me/theorems/802eb417-4bd2-4beb-81d0-d4cc669c1cf2
-- title:
--   CMLattice: exists basis of cm Type
-- statement:
--   The CMLattice construction uses the exists basis of cm Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/EqTopOfForallEmbAllMem.lean#L122-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/EqTopOfForallEmbAllMem.lean#L122-L165

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

theorem GlobalTheory.CMLattice.exists_basis_of_cmType (Ψ : Finset (E →+* ℂ))
    (h : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (r : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) :
    ∃ b : Module.Basis (Fin (2 * (Ψ.card * r))) ℝ (Ψ → Fin r → ℂ),
      ∀ y, y ∈ Submodule.span ℤ (Set.range b) ↔ ∃ v ∈ Λ, embAll Ψ r v = y := by sorry
