-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermFrame_adapted_cons
-- name    : GlobalTheory.CompanionTheory.HermFrame.adapted_cons
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:52.105171+00:00
-- url     : https://prove2.me/theorems/5ae8674f-463c-448a-b91d-3aa2742d2193
-- title:
--   Herm Frame: adapted cons
-- statement:
--   The Herm Frame construction uses the adapted cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FrameOfAnisotropicPlaneSplitting.lean#L100-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FrameOfAnisotropicPlaneSplitting.lean#L100-L125

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FrameOfAnisotropicPlaneSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermFrame
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

theorem GlobalTheory.CompanionTheory.HermFrame.adapted_cons {U : Submodule L V} {e f : V} {l : ℕ} {e' f' : Fin l → U} {W' : Submodule L U}
    {u0 : L} {u' : Fin l → L} {Λ : AddSubgroup V}
    (hsp : ∀ (a b : L), ∀ w ∈ U, (a • e + b • f + w ∈ Λ ↔ ‖a‖ ≤ ‖u0‖ ∧ ‖b‖ ≤ ‖u0‖⁻¹ ∧ w ∈ Λ))
    (had : IsAdapted (fun x y : U => h x y) e' f' W' u' (Λ.comap U.subtype.toAddMonoidHom)) :
    IsAdapted h (Fin.cons e fun i => (e' i : V) : Fin (l + 1) → V)
      (Fin.cons f fun i => (f' i : V) : Fin (l + 1) → V) (W'.map U.subtype)
      (Fin.cons u0 u' : Fin (l + 1) → L) Λ := by sorry
