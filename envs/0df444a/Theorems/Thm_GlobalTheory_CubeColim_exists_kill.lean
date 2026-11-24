-- Prove2me | Theorems.Thm_GlobalTheory_CubeColim_exists_kill
-- name    : GlobalTheory.CubeColim.exists_kill
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:35.818798+00:00
-- url     : https://prove2.me/theorems/33e2d50f-f75e-4d7e-9dc1-e777f0d9b120
-- title:
--   Cube Colim: exists kill
-- statement:
--   The Cube Colim construction uses the exists kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechComplexDirectLimit.lean#L40-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechComplexDirectLimit.lean#L40-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechComplexDirectLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Filter
open GlobalTheory
open GlobalTheory.CubeColim
variable {ι : Type} [LinearOrder ι] [Fintype ι]

theorem GlobalTheory.CubeColim.exists_kill {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h2 : ∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e),
      μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'')
    (h4 : ∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 →
      ∃ j, (μ j c (c + j) rfl).app s a = 0)
    {m : ℕ} (hm : 0 < m) (c : ℕ) (x : Cube.Term (A c) m) (hx : Cube.termMap (ρ c) m x = 0) :
    ∃ J, Cube.termMap (μ J c (c + J) rfl) m x = 0 := by sorry
