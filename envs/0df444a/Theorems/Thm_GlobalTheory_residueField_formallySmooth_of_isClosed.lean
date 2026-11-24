-- Prove2me | Theorems.Thm_GlobalTheory_residueField_formallySmooth_of_isClosed
-- name    : GlobalTheory.residueField_formallySmooth_of_isClosed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:22.561493+00:00
-- url     : https://prove2.me/theorems/1d6cdfa2-5ca5-4eb9-9565-70ec06504125
-- title:
--   Global Theory: residue Field formally Smooth of is Closed
-- statement:
--   The Global Theory construction uses the residue Field formally Smooth of is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueFieldFormallySmooth.lean#L8-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueFieldFormallySmooth.lean#L8-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsEtCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueFieldFormallySmooth
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

theorem GlobalTheory.residueField_formallySmooth_of_isClosed : ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k) [LocallyOfFiniteType f] (U : X.Opens) (x : X) (hxU : x ∈ U), IsClosed ({x} : Set X) → letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra; Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by sorry
