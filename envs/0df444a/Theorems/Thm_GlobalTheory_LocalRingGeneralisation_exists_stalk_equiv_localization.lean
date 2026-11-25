-- Prove2me | Theorems.Thm_GlobalTheory_LocalRingGeneralisation_exists_stalk_equiv_localization
-- name    : GlobalTheory.LocalRingGeneralisation.exists_stalk_equiv_localization
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:59.270821+00:00
-- url     : https://prove2.me/theorems/e639553d-d61f-4282-b345-399ac432e529
-- title:
--   Local Ring Generalisation: exists stalk equiv localization
-- statement:
--   The Local Ring Generalisation construction uses the exists stalk equiv localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/StalkGenerizationGermCompat.lean#L34-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/StalkGenerizationGermCompat.lean#L34-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_StalkGenerizationGermCompat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open GlobalTheory GlobalTheory.LocalRingGeneralisation

theorem GlobalTheory.LocalRingGeneralisation.exists_stalk_equiv_localization : ∀ {X : Scheme.{0}} (x : X) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime], ∃ (q : X) (e : X.presheaf.stalk q ≃+* Localization.AtPrime p), q ⤳ x ∧ ∀ (U : X.Opens) (hq : q ∈ U) (hx : x ∈ U) (s : Γ(X, U)), e ((X.presheaf.germ U q hq).hom s) = algebraMap (X.presheaf.stalk x) (Localization.AtPrime p) ((X.presheaf.germ U x hx).hom s) := by sorry
