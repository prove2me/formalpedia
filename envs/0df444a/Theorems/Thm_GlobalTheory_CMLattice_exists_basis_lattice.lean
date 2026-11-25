-- Prove2me | Theorems.Thm_GlobalTheory_CMLattice_exists_basis_lattice
-- name    : GlobalTheory.CMLattice.exists_basis_lattice
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:11:57.804668+00:00
-- url     : https://prove2.me/theorems/8964275d-9ce4-4870-9e19-4971b7621897
-- title:
--   CMLattice: exists basis lattice
-- statement:
--   The CMLattice construction uses the exists basis lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/EqTopOfForallEmbAllMem.lean#L167-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/EqTopOfForallEmbAllMem.lean#L167-L172

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

theorem GlobalTheory.CMLattice.exists_basis_lattice (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) :
    ∃ b : Module.Basis (Fin (2 * (X.Ψ.card * r))) ℝ (X.Ψ → Fin r → ℂ),
      ∀ y, y ∈ Submodule.span ℤ (Set.range b) ↔
        ∃ v ∈ X.Λ, (fun τ : X.Ψ => Data.emb τ.1 v) = y := by sorry
