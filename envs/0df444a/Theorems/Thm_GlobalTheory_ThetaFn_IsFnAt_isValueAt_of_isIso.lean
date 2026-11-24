-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFn_IsFnAt_isValueAt_of_isIso
-- name    : GlobalTheory.ThetaFn.IsFnAt.isValueAt_of_isIso
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:04:53.277489+00:00
-- url     : https://prove2.me/theorems/8e884d0f-39ed-4127-b4d7-a0005206239c
-- title:
--   Is Fn At: is Value At of is Iso
-- statement:
--   The Is Fn At construction uses the is Value At of is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L501-L513
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L501-L513

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}
variable (u p)
variable {u p}

theorem GlobalTheory.ThetaFn.IsFnAt.isValueAt_of_isIso [IsIso p] {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {θ : (Fin g → ℂ) → ℂ} (h : IsFnAt u p k s θ) {x : T ⟶ A} {z : Fin g → ℂ}
    (hx : p ≫ x = u.ex z)
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => k))}
    {v : Γ(T.left, ⊤)} (hv : ∀ j : Fin 1 → L.ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) →
      valAt' p.left ⊤ v * valAt' p.left (LB.wchart L (fun _ : Fin 1 => x.left) j) (τ.s j).val =
        θ z * u.fr (j 0) z ^ k) : IsValueAt A L k s x τ v := by sorry
