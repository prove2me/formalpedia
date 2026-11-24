-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_DiagLattice_exists_symR_diag
-- name    : GlobalTheory.FunObj.DiagLattice.exists_symR_diag
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:40:32.49752+00:00
-- url     : https://prove2.me/theorems/7e1c7157-fbe9-43a5-adeb-719e972897cd
-- title:
--   Diag Lattice: exists sym R diag
-- statement:
--   The Diag Lattice construction uses the exists sym R diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsKOOfDet.lean#L49-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsKOOfDet.lean#L49-L180

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.DiagLattice

theorem GlobalTheory.FunObj.DiagLattice.exists_symR_diag : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (d : Fin c → kˣ) (H : GL (n ⊕ Fin c) k),
  (∀ i : Fin c, ∃ v : n ⊕ Fin c → k, v (Sum.inr i) = 1 ∧ (∀ l : Fin c, i < l → v (Sum.inr l) = 0) ∧ (i.val < (c + 1) / 2 → ∀ r, v (Sum.inl r) = 0) ∧ ∀ t, ((H⁻¹).val *ᵥ ((d i : k) • v)) t ∈ 𝒪[k]) →
  (∀ (i : Fin c) (y : n ⊕ Fin c → k), (∀ t, y t ∈ 𝒪[k]) → (∀ l : Fin c, i < l → (H.val *ᵥ y) (Sum.inr l) = 0) → (i.val < c / 2 → ∀ r, (H.val *ᵥ y) (Sum.inl r) = 0) → valuation k ((H.val *ᵥ y) (Sum.inr i)) ≤ valuation k (d i : k)) →
  ∃ r ∈ symR k n c, ∃ w ∈ KO k (n ⊕ Fin c), H = r * diagGL (Sum.elim (fun _ => 1) d) * w := by sorry
