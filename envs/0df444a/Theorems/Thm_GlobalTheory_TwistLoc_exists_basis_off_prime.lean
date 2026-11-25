-- Prove2me | Theorems.Thm_GlobalTheory_TwistLoc_exists_basis_off_prime
-- name    : GlobalTheory.TwistLoc.exists_basis_off_prime
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:09:08.812321+00:00
-- url     : https://prove2.me/theorems/0625c516-5a83-4162-a996-22bda76183e9
-- title:
--   Twist Loc: exists basis off prime
-- statement:
--   The Twist Loc construction uses the exists basis off prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTwistBasisOffPrime.lean#L331-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTwistBasisOffPrime.lean#L331-L394

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistLoc

theorem GlobalTheory.TwistLoc.exists_basis_off_prime : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), (∃ W : (Spec (CommRingCat.of R)).Opens, genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W)) → ∀ (p : Ideal R) [p.IsPrime] (k : ℕ), 1 ≤ k → ∀ α : D.X, ∃ b : Fin (k ^ D.P.g) → D.SecB k α, ∀ (R' : Type) [CommRing R'] (f : R →+* R'), (∀ s ∉ p, IsUnit (f s)) → ∀ b' : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i) (DegPre.famε k)), (∀ i, IsPullSecLC D.P.L (DegPre.famφB D α) (DegPre.famε k) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left (b i) (b' i)) → IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.P.A) _ b' := by sorry
