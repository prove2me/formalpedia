-- Prove2me | Theorems.Thm_GlobalTheory_Pat_PhiFin_finite_cocycles
-- name    : GlobalTheory.Pat.PhiFin.finite_cocycles
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:41:21.308898+00:00
-- url     : https://prove2.me/theorems/003c4d29-b794-4910-9ec0-f272e24b85ab
-- title:
--   Phi Fin: finite cocycles
-- statement:
--   The Phi Fin construction uses the finite cocycles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L194-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L194-L226

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
noncomputable section
open IsLocalRing
open GlobalTheory GlobalTheory.Pat

theorem GlobalTheory.Pat.PhiFin.finite_cocycles {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (hG : PhiFin l G) {M : Type} [AddCommGroup M] [Finite M]
    (hl : ∀ m : M, l • m = 0) (H : Subgroup G) (hH : IsOpen (H : Set G)) (L R : G → M → M)
    (hL : ∀ h ∈ H, ∀ m, L h m = m) (hR : ∀ h ∈ H, ∀ m, R h m = m) :
    {f : G → M | IsLocallyConstant f ∧ ∀ g h, f (g * h) = L g (f h) + R h (f g)}.Finite := by sorry
