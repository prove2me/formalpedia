-- Prove2me | Theorems.Thm_GlobalTheory_SatBlocks_exists_projector
-- name    : GlobalTheory.SatBlocks.exists_projector
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:09.340452+00:00
-- url     : https://prove2.me/theorems/8bb8caaf-bc22-4f59-817c-9bb7f68453c3
-- title:
--   Sat Blocks: exists projector
-- statement:
--   The Sat Blocks construction uses the exists projector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SaturatedBlocksSummand.lean#L39-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SaturatedBlocksSummand.lean#L39-L81

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SaturatedBlocksSummand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.SatBlocks

theorem GlobalTheory.SatBlocks.exists_projector {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {O A : Type}
    [DecidableEq A] {n : A → ℕ} {d : ℕ} (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C)
    (u : (Σ a : A, Fin (n a)) → Fin d → C)
    (hM : ∀ x i j, M x i j ∈ intRing v) (he : ∀ a x, em a x ∈ intRing v)
    (hu : ∀ x q, (M x).mulVec (u q) = em q.1 x • u q)
    (hs : ∀ a a', a ≠ a' → ∃ x, v (em a x - em a' x) = 0) (a : A) (S : Finset A) (ha : a ∉ S) :
    ∃ (P : Matrix (Fin d) (Fin d) C) (c : A → C), (∀ i j, P i j ∈ intRing v) ∧
      (∀ q, P.mulVec (u q) = c q.1 • u q) ∧ c a = 1 ∧ ∀ b ∈ S, c b = 0 := by sorry
