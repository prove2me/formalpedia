-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResMult_not_isRoot_cofactor
-- name    : GlobalTheory.UnitLemma.Unr.ResMult.not_isRoot_cofactor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:35:13.897272+00:00
-- url     : https://prove2.me/theorems/589fbe38-4a2e-4cc2-b74f-aff4887d53d4
-- title:
--   Res Mult: not is Root cofactor
-- statement:
--   The Res Mult construction uses the not is Root cofactor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotIsRootResidueCofactorUnramifiedExt.lean#L12-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotIsRootResidueCofactorUnramifiedExt.lean#L12-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceIntOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsRootResidueCofactorUnramifiedExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.ResMult
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem GlobalTheory.UnitLemma.Unr.ResMult.not_isRoot_cofactor : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ s : K'.O,
    (∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y =
      f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z) →
    ∀ (p : K.O[X]) (r c : K'.O[X]), p.Monic → r.Monic →
      r.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ r.natDegree →
      p.natDegree = d * r.natDegree →
      p.map (φ.comp (algebraMap K.O K.E)) = (r * c).map (algebraMap K'.O K'.E) →
      ¬ (c.map (IsLocalRing.residue K'.O)).IsRoot (IsLocalRing.residue K'.O s) := by sorry
