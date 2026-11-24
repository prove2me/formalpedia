-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFourier_valF_sum
-- name    : GlobalTheory.TorsionFourier.valF_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:09:07.331019+00:00
-- url     : https://prove2.me/theorems/88bc276c-fb90-4aa7-8905-7ac152e1d957
-- title:
--   Torsion Fourier: val F sum
-- statement:
--   The Torsion Fourier construction uses the val F sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PartVanishesOnTorusTorsionFourier.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PartVanishesOnTorusTorsionFourier.lean#L17-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPointTranslatePure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinsuppEqZeroOfSumTorsionCharactersEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PartVanishesOnTorusTorsionFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.TorsionFourier
variable {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens}

theorem GlobalTheory.TorsionFourier.valF_sum (h : ⊤ ≤ x ⁻¹ᵁ U) {J : Type} (A : Finset J) (a : J → Γ(X, U)) :
    valF x U (∑ j ∈ A, a j) = ∑ j ∈ A, valF x U (a j) := by sorry
