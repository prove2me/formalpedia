-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_exists_basis_lat
-- name    : GlobalTheory.UnitLemma.SgnProd.exists_basis_lat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:37:13.813961+00:00
-- url     : https://prove2.me/theorems/c7ea2e85-d649-4b26-a401-f268e7d9ab71
-- title:
--   Sgn Prod: exists basis lat
-- statement:
--   The Sgn Prod construction uses the exists basis lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SgnLatProdEqEtaResultantMul.lean#L35-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SgnLatProdEqEtaResultantMul.lean#L35-L47

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

theorem GlobalTheory.UnitLemma.SgnProd.exists_basis_lat (K : UQ) {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [Module.Finite K.E V] (L : Submodule K.O V) (hfg : L.FG) (hsp : Submodule.span K.E (L : Set V) = ⊤) :
    ∃ e : Module.Basis (Fin (Module.finrank K.E V)) K.E V, Submodule.span K.O (Set.range e) = L := by sorry
