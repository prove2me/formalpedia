-- Prove2me | Theorems.Thm_GlobalTheory_KeyPBScale_keyPB_scale
-- name    : GlobalTheory.KeyPBScale.keyPB_scale
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:05:47.04189+00:00
-- url     : https://prove2.me/theorems/2c5f23b1-8f92-5f3b-8726-3f73bc19a0bd
-- title:
--   Key PBScale: key PB scale
-- statement:
--   The Key PBScale construction uses the key PB scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LieBaseChange.lean#L35-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LieBaseChange.lean#L35-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PwIsoIsGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DualNumberRingHomExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_LieCombBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LieBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyPBScale

theorem GlobalTheory.KeyPBScale.keyPB_scale : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (P : Out.PolAV (Sp R)) (hg rig hr th hth v hv th' hth' v' hv') (a : R) (M : Matrix (Fin P.g) (Fin P.g) R) (Q : Out.PolAV (Sp R')) (e : Q.g = P.g) (hgQ rigQ hrQ s hs u hu s' hs' u' hu'), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → (∀ i, LB.Sec.f s' i = constFn Q.A.hom _ (f a) * LB.Sec.f s i) → (∀ i : Fin Q.g, IsLieComb (fun j : Fin Q.g => f (M (i.cast e) (j.cast e))) u (u' i)) → KeyPB (⟨Q, hgQ, rigQ, hrQ, s, hs, u, hu⟩ : KeyIn R') (⟨P, hg, rig, hr, th, hth, v, hv⟩ : KeyIn R) f → KeyPB (⟨Q, hgQ, rigQ, hrQ, s', hs', u', hu'⟩ : KeyIn R') (⟨P, hg, rig, hr, th', hth', v', hv'⟩ : KeyIn R) f := by sorry
