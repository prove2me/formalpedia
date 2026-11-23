-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_bil_sm_right
-- name    : GlobalTheory.DRFil.bil_sm_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:45.984083+00:00
-- url     : https://prove2.me/theorems/0b244d31-dfbf-4868-9ffb-105b41d5a9a3
-- title:
--   DRFil: bil sm right
-- statement:
--   The DRFil construction uses the bil sm right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfForallMemFilV.lean#L82-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfForallMemFilV.lean#L82-L95

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

theorem GlobalTheory.DRFil.bil_sm_right (β : V →ₗ[LL] V' →ₗ[LL] V'') (r : LL ⊗[Qp] F) (x : V ⊗[Qp] F) (y : V' ⊗[Qp] F) :
    bil Qp F β x (sm Qp F LL V' r y) = sm Qp F LL V'' r (bil Qp F β x y) := by sorry
