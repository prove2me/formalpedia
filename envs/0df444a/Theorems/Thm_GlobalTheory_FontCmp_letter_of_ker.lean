-- Prove2me | Theorems.Thm_GlobalTheory_FontCmp_letter_of_ker
-- name    : GlobalTheory.FontCmp.letter_of_ker
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:32:52.557825+00:00
-- url     : https://prove2.me/theorems/dbc4245b-3a6c-448a-87b9-85398822b593
-- title:
--   Font Cmp: letter of ker
-- statement:
--   The Font Cmp construction uses the letter of ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FontaineFormalismTensorEquiv.lean#L474-L570
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FontaineFormalismTensorEquiv.lean#L474-L570

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FontCmp
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem GlobalTheory.FontCmp.letter_of_ker [Algebra.IsSeparable Qp K₀]
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (hr : LinearMap.range (TensorMultiplication.mulDcris PD ρ ρ') = Dcris PD (ρ.tprod ρ'))
    (hk : LinearMap.ker (TensorMultiplication.mulDcris PD ρ ρ') = TensorMultiplication.balK PD ρ ρ') (τ : K₀ →ₐ[Qp] LL) :
    Function.Injective ((CrystallineSubrepresentation.prodB (LL := LL)).comp
        (TensorProduct.map (DcrisL PD ρ τ).subtype (DcrisL PD ρ' τ).subtype)) ∧
      LinearMap.range ((CrystallineSubrepresentation.prodB (LL := LL)).comp
        (TensorProduct.map (DcrisL PD ρ τ).subtype (DcrisL PD ρ' τ).subtype)) =
        DcrisL PD (ρ.tprod ρ') τ := by sorry
