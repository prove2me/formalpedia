-- Prove2me | Theorems.Thm_GlobalTheory_HolHomOnto_exists_isDerivAt_of_surjective
-- name    : GlobalTheory.HolHomOnto.exists_isDerivAt_of_surjective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:14:34.618893+00:00
-- url     : https://prove2.me/theorems/257fe2f1-af83-4299-8b2b-66e85c180c72
-- title:
--   Hol Hom Onto: exists is Deriv At of surjective
-- statement:
--   The Hol Hom Onto construction uses the exists is Deriv At of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsDerivAtOfSurjective.lean#L94-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsDerivAtOfSurjective.lean#L94-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HolDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsDerivAtOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HolHomOnto
open GlobalTheory.TangentOrigin GlobalTheory.HolHom

theorem GlobalTheory.HolHomOnto.exists_isDerivAt_of_surjective : ∀ (G : Over (Sp ℂ)) [GrpObj G] (y : Sp ℂ ⟶ Sp ℂ), y = 𝟙 _ → Smooth G.hom → ∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) → ∀ v : Sp (DualNumber ℂ) ⟶ G.left, v ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = (e 0).left → ∃ w, GlobalTheory.HolHom.IsDerivAt (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) 0 w v := by sorry
