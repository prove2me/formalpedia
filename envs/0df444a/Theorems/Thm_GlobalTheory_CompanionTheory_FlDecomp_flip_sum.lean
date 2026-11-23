-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_flip_sum
-- name    : GlobalTheory.CompanionTheory.FlDecomp.flip_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:07.965163+00:00
-- url     : https://prove2.me/theorems/7c34c704-f022-49c8-81e0-d465373b9ac5
-- title:
--   Fl Decomp: flip sum
-- statement:
--   The Fl Decomp construction uses the flip sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L252-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L252-L259

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlDecomp
open CompanionTheory.Rg.FlB
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
variable {s : L →+* L} {δ : L} {h : V → V → L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}

theorem GlobalTheory.CompanionTheory.FlDecomp.flip_sum (F : Fin l → Prop) [DecidablePred F] (c : L) (a b : Fin l → L) :
    ∑ i, a i • (if F i then f i else e i) + ∑ i, b i • (if F i then c • e i else f i) =
      ∑ i, (if F i then c * b i else a i) • e i + ∑ i, (if F i then a i else b i) • f i := by sorry
