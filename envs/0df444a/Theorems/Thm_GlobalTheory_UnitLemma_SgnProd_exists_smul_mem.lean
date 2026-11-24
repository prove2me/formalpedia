-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_exists_smul_mem
-- name    : GlobalTheory.UnitLemma.SgnProd.exists_smul_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:34:16.188345+00:00
-- url     : https://prove2.me/theorems/593caccd-fc2a-4013-92e9-94542a271ef1
-- title:
--   Sgn Prod: exists smul mem
-- statement:
--   The Sgn Prod construction uses the exists smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SgnLatProdEqEtaResultantMul.lean#L49-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SgnLatProdEqEtaResultantMul.lean#L49-L63

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

theorem GlobalTheory.UnitLemma.SgnProd.exists_smul_mem (K : UQ) {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [Module.Finite K.E V] (L : Submodule K.O V) (hfg : L.FG) (hsp : Submodule.span K.E (L : Set V) = ⊤) (y : V) :
    ∃ s : K.O, s ≠ 0 ∧ s • y ∈ L := by sorry
