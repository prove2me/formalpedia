-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_trace_mat_toMatrix
-- name    : GlobalTheory.UnitLemma.SgnProd.trace_mat_toMatrix
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:34:33.20149+00:00
-- url     : https://prove2.me/theorems/f7db4d65-d643-41e9-903a-cf201b444d60
-- title:
--   Sgn Prod: trace mat to Matrix
-- statement:
--   The Sgn Prod construction uses the trace mat to Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SgnLatProdEqEtaResultantMul.lean#L105-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SgnLatProdEqEtaResultantMul.lean#L105-L112

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

theorem GlobalTheory.UnitLemma.SgnProd.trace_mat_toMatrix {E A : Type} [Field E] [CommRing A] [Algebra E A] {ι κ : Type} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι E A) (x : κ → A) (f : ι → A) :
    (Matrix.of fun k l => Algebra.trace E A (x k * f l)) =
      (Matrix.of fun k i => Algebra.trace E A (x k * b i)) * b.toMatrix f := by sorry
