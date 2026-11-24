-- Prove2me | Theorems.Thm_GlobalTheory_TorusKer_valsAt_torus_eq_one_iff
-- name    : GlobalTheory.TorusKer.valsAt_torus_eq_one_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:10:06.750641+00:00
-- url     : https://prove2.me/theorems/49731789-2ecb-42f7-8df2-29fd66a4b493
-- title:
--   Torus Ker: vals At torus eq one iff
-- statement:
--   The Torus Ker construction uses the vals At torus eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ZValuationsAtIndicesTorusEqOneIff.lean#L7-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ZValuationsAtIndicesTorusEqOneIff.lean#L7-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValsAtApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ZValuationsAtIndicesTorusEqOneIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma
open GlobalTheory GlobalTheory.TorusKer

theorem GlobalTheory.TorusKer.valsAt_torus_eq_one_iff (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G)
    (hT : ∀ t, t ∈ T ↔ t * τ t = 1) (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ)
    (hs : ∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x)))
    (r : ℕ) (e : Fin r → ι) (hcov : ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) (t : T) :
    (valsAt w e).comp T.subtype t = 1 ↔ ∀ i, Multiplicative.toAdd (w i (t : G)) = 0 := by sorry
