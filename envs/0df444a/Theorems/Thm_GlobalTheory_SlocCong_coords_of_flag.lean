-- Prove2me | Theorems.Thm_GlobalTheory_SlocCong_coords_of_flag
-- name    : GlobalTheory.SlocCong.coords_of_flag
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:44:00.702681+00:00
-- url     : https://prove2.me/theorems/ad9f75fd-6d4d-42fc-b5a3-801f1c58acf4
-- title:
--   Sloc Cong: coords of flag
-- statement:
--   The Sloc Cong construction uses the coords of flag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermFamiliesCongrModUnitriangular.lean#L117-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermFamiliesCongrModUnitriangular.lean#L117-L204

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermFamiliesCongrModUnitriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.S
open GlobalTheory GlobalTheory.SlocCong

theorem GlobalTheory.SlocCong.coords_of_flag {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V]
    [Module E V] {H : Loc.HermSp M V} {r : ℕ} (Fr : LocNG.FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))
    (g : V ≃ₗ[E] V) (hg : ∀ a, g (Fr.f a) - Fr.f a ∈ Submodule.span E (Fr.f '' {c | c < a}))
    (y : Fin (r + 1) → V) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hB : ∀ a b, b < a → B a b = 0) (hBO : ∀ a, B a a ∈ M.L.O)
    (hy : ∀ b, y b = ∑ a, B a b • Fr.f a) (hyL : ∀ b, g (y b) ∈ Fr.LamStd L) :
    ∃ W : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, b < a → W a b = 0) ∧ (∀ a, W a a = B a a) ∧
      (∀ a b, W a b ∈ M.L.O) ∧ ∀ b, g (y b) = ∑ c, W c b • Fr.f c := by sorry
