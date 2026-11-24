-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_det_trace_lift
-- name    : GlobalTheory.UnitLemma.SgnProd.det_trace_lift
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:29:32.191251+00:00
-- url     : https://prove2.me/theorems/8a6e4f60-4565-4097-bf98-f99ff7e63e23
-- title:
--   Sgn Prod: det trace lift
-- statement:
--   The Sgn Prod construction uses the det trace lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SgnLatProdEqEtaResultantMul.lean#L201-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SgnLatProdEqEtaResultantMul.lean#L201-L252

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatProdEqEtaResultantMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.SgnProd
open Module

theorem GlobalTheory.UnitLemma.SgnProd.det_trace_lift {E A₁ A₂ : Type} [Field E] [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    {a b : ℕ} (g : A₁ × A₂) (e₁ : Basis (Fin a) E A₁) (e₂ : Basis (Fin b) E A₂) (x : Fin b → A₁ × A₂)
    (hx : ∀ j, (x j).2 = e₂ j) :
    (Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂)
      (g ^ (k : ℕ) * Fin.addCases (fun i => ((e₁ i, 0) : A₁ × A₂)) x l)).det =
    (Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂)
      (g ^ (k : ℕ) * Fin.addCases (fun i => ((e₁ i, 0) : A₁ × A₂)) (fun j => ((0, e₂ j) : A₁ × A₂)) l)).det := by sorry
