-- Prove2me | Theorems.Thm_GlobalTheory_GalOfCusp_IsAttached_frob
-- name    : GlobalTheory.GalOfCusp.IsAttached.frob
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:48:55.983824+00:00
-- url     : https://prove2.me/theorems/836037a5-8bf2-4db1-b6c5-23fc529a320f
-- title:
--   Is Attached: frob
-- statement:
--   The Is Attached construction uses the frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/TrivialOnInertiaOfUnr.lean#L94-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/TrivialOnInertiaOfUnr.lean#L94-L104

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__TrivialOnInertiaOfUnr_d5f82434e8467b70
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GalOfCusp
open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open scoped Matrix
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)
variable {A}
variable {i : N.Loc} {a : ℕ} {π : A.CG a} {s : ℝ} {r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))}

theorem GlobalTheory.GalOfCusp.IsAttached.frob (h : IsAttached A i π s r) {w : PlE H} (hw : w ∉ placesOver H.E (N.l i))
    (hu : A.unr (A.locG π w)) :
    (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), r σ = 1) ∧
    ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w →
      IsFrob (F := H.E) B (normV w) σ →
      (r σ : Matrix (Fin a) (Fin a) (Qbar (N.l i))).charpoly.map (A.iotaQC i).toRingHom =
        galPol A (A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2)) := by sorry
