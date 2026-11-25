-- Prove2me | Theorems.Thm_GlobalTheory_T_residue_field_formally_smooth
-- name    : GlobalTheory.T.residue_field_formally_smooth
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:27.279323+00:00
-- url     : https://prove2.me/theorems/97c5db89-4380-5da3-8cad-76d826ba46ab
-- title:
--   T: residue field formally smooth
-- statement:
--   The T construction uses the residue field formally smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/ResidueFieldFormallySmooth.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/ResidueFieldFormallySmooth.lean#L9-L10

import Mathlib
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsEtCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueFieldFormallySmooth
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_ResidueFieldFormallySmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct

theorem GlobalTheory.T.residue_field_formally_smooth : ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k) [LocallyOfFiniteType f] (U : X.Opens) (x : X) (hxU : x ∈ U), IsClosed ({x} : Set X) → letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra; Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by sorry
