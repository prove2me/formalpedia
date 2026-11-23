-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_bil_sm_left
-- name    : GlobalTheory.DRFil.bil_sm_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:38.997498+00:00
-- url     : https://prove2.me/theorems/20cf36df-f602-408c-a8f8-ffc27859e8a1
-- title:
--   DRFil: bil sm left
-- statement:
--   The DRFil construction uses the bil sm left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfForallMemFilV.lean#L67-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfForallMemFilV.lean#L67-L80

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
variable {Qp : Type} [Field Qp] (F : Type) [CommRing F] [Algebra Qp F]
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
variable {F}

theorem GlobalTheory.DRFil.bil_sm_left (β : V →ₗ[LL] V' →ₗ[LL] V'') (r : LL ⊗[Qp] F) (x : V ⊗[Qp] F) (y : V' ⊗[Qp] F) :
    bil Qp F β (sm Qp F LL V r x) y = sm Qp F LL V'' r (bil Qp F β x y) := by sorry
