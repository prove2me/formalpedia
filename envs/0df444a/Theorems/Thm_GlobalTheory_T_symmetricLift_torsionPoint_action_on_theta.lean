-- Prove2me | Theorems.Thm_GlobalTheory_T_symmetricLift_torsionPoint_action_on_theta
-- name    : GlobalTheory.T.symmetricLift_torsionPoint_action_on_theta
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:28.4545+00:00
-- url     : https://prove2.me/theorems/482c6523-0ee9-450f-8e48-2b5e93fb51b8
-- title:
--   T: symmetric Lift torsion Point action on theta
-- statement:
--   The T construction uses the symmetric Lift torsion Point action on theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SymmetricLiftTorsionPointActionOnThetaStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SymmetricLiftTorsionPointActionOnThetaStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymmetricLiftTorsionPointActionOnTheta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymmetricLiftTorsionPointActionOnThetaStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.T.symmetricLift_torsionPoint_action_on_theta : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (N : ℕ) (l : u.Λ) (f : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (x : T ⟶ P.A) (U : Out.ThetaGrp P.A P.L ((N : ℤ) ^ 2) T) (s s' : LB.Sec (Out.LPow P.A P.L ((N : ℤ) ^ 2) T)), u.IsAH Hm χ → Odd N → p ≫ x = u.ex (((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ)) → Out.SymLift P.A P.L ((N : ℤ) ^ 2) (N ^ 2) x U → Out.IsActOf P.A P.L ((N : ℤ) ^ 2) U s s' → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s.f j) = f z * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s'.f j) = (χ l * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm l l - Real.pi * hermForm Hm z l) * f (z + ((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ))) * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) := by sorry
