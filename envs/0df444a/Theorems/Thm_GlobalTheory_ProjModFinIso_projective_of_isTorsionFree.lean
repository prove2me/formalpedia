-- Prove2me | Theorems.Thm_GlobalTheory_ProjModFinIso_projective_of_isTorsionFree
-- name    : GlobalTheory.ProjModFinIso.projective_of_isTorsionFree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:42.524101+00:00
-- url     : https://prove2.me/theorems/b7d9050a-3109-4afb-9b2b-266742f3e6be
-- title:
--   Proj Mod Fin Iso: projective of is Torsion Free
-- statement:
--   The Proj Mod Fin Iso construction uses the projective of is Torsion Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinitelyManyIsoClassesProjectiveNumberField.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinitelyManyIsoClassesProjectiveNumberField.lean#L18-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.ProjModFinIso
variable {R : Type} [CommRing R] [IsDedekindDomain R]

theorem GlobalTheory.ProjModFinIso.projective_of_isTorsionFree (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Projective R M := by sorry
