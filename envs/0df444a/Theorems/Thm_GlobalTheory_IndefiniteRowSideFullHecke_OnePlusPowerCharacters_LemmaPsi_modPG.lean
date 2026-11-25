-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OnePlusPowerCharacters_LemmaPsi_modPG
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi.modPG
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:08:56.148716+00:00
-- url     : https://prove2.me/theorems/c52bc837-e968-5eb8-bb9f-7d41c90228bc
-- title:
--   Lemma Psi: mod PG
-- statement:
--   The Lemma Psi construction uses the mod PG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/OnePlusPowerAssembly.lean#L78-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/OnePlusPowerAssembly.lean#L78-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_OnePlusPowerAssembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam

theorem GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi.modPG (h : LemmaPsi) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (hl : 5 ≤ l)
    (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (hι : IsCyclotomic R ι) :
    ∃ ψ : k⸨X⸩ →ₗ[k] k⸨X⸩, IsPsi l ι ψ ∧ PsiRing R ψ ∧
      ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
        [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
        [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V) (i : ZMod n),
        ∃ Ψ : V →ₗ[k] V, PsiMod l ψ (D.φ i) (D.γ (i - 1)) (D.γ i) Ψ := by sorry
