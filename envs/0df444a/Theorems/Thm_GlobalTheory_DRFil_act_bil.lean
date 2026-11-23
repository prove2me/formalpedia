-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_act_bil
-- name    : GlobalTheory.DRFil.act_bil
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:00.313806+00:00
-- url     : https://prove2.me/theorems/a88ad872-7ba7-4448-81c6-b817de89b29a
-- title:
--   DRFil: act bil
-- statement:
--   The DRFil construction uses the act bil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfForallMemFilV.lean#L370-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfForallMemFilV.lean#L370-L381

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']

theorem GlobalTheory.DRFil.act_bil (ρ : Representation LL G V) (ρ' : Representation LL G V') (ρ'' : Representation LL G V'')
    (β : V →ₗ[LL] V' →ₗ[LL] V'') (hβ : ∀ g v w, β (ρ g v) (ρ' g w) = ρ'' g (β v w)) (g : G)
    (x : V ⊗[Qp] F) (y : V' ⊗[Qp] F) :
    actVdR PD ρ'' g (bil Qp F β x y) = bil Qp F β (actVdR PD ρ g x) (actVdR PD ρ' g y) := by sorry
