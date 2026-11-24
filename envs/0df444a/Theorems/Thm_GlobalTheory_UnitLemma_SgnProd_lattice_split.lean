-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_lattice_split
-- name    : GlobalTheory.UnitLemma.SgnProd.lattice_split
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:33:53.571256+00:00
-- url     : https://prove2.me/theorems/448f7892-8014-4768-a48a-5d5d506d724f
-- title:
--   Sgn Prod: lattice split
-- statement:
--   The Sgn Prod construction uses the lattice split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SgnLatProdEqEtaResultantMul.lean#L120-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SgnLatProdEqEtaResultantMul.lean#L120-L193

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

theorem GlobalTheory.UnitLemma.SgnProd.lattice_split (K : UQ) (V₁ V₂ : Type) [AddCommGroup V₁] [Module K.E V₁] [Module K.O V₁]
    [IsScalarTower K.O K.E V₁] [Module.Finite K.E V₁] [AddCommGroup V₂] [Module K.E V₂] [Module K.O V₂]
    [IsScalarTower K.O K.E V₂] [Module.Finite K.E V₂] (M : Submodule K.O (V₁ × V₂)) (hfg : M.FG)
    (hsp : Submodule.span K.E (M : Set (V₁ × V₂)) = ⊤) :
    ∃ (e₁ : Basis (Fin (finrank K.E V₁)) K.E V₁) (e₂ : Basis (Fin (finrank K.E V₂)) K.E V₂)
      (x : Fin (finrank K.E V₂) → V₁ × V₂),
      Submodule.span K.O (Set.range e₁) = M.comap (LinearMap.inl K.O V₁ V₂) ∧
      Submodule.span K.O (Set.range e₂) = M.map (LinearMap.snd K.O V₁ V₂) ∧
      (∀ j, (x j).2 = e₂ j) ∧
      Submodule.span K.O (Set.range (Fin.addCases (fun i => ((e₁ i, 0) : V₁ × V₂)) x)) = M := by sorry
