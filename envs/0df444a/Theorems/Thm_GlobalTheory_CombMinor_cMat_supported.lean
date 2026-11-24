-- Prove2me | Theorems.Thm_GlobalTheory_CombMinor_cMat_supported
-- name    : GlobalTheory.CombMinor.cMat_supported
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:15:02.746722+00:00
-- url     : https://prove2.me/theorems/62ea8112-f941-4c7a-a119-5b83ce18f3ab
-- title:
--   Comb Minor: c Mat supported
-- statement:
--   The Comb Minor construction uses the c Mat supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ProdDetMemHaO.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ProdDetMemHaO.lean#L26-L36

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdDetMemHaO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MvPolynomial Formalism.L2.Pj Formalism.L2.Pj.Crude
open GlobalTheory GlobalTheory.CombMinor
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k]

theorem GlobalTheory.CombMinor.cMat_supported (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k) (S : Set (Letter Ty r n))
    (h : ∀ ρ i b, B ρ b ≠ 0 → (⟨τ, i, b⟩ : Letter Ty r n) ∈ S) :
    (cMat τ s hs B).det ∈ supported k S := by sorry
