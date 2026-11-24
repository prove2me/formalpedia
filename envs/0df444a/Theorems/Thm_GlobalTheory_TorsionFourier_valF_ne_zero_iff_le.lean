-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFourier_valF_ne_zero_iff_le
-- name    : GlobalTheory.TorsionFourier.valF_ne_zero_iff_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:08:57.435912+00:00
-- url     : https://prove2.me/theorems/2c119ecc-9a24-4a78-81e5-c3145336481f
-- title:
--   Torsion Fourier: val F ne zero iff le
-- statement:
--   The Torsion Fourier construction uses the val F ne zero iff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PartVanishesOnTorusTorsionFourier.lean#L21-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PartVanishesOnTorusTorsionFourier.lean#L21-L37

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

theorem GlobalTheory.TorsionFourier.valF_ne_zero_iff_le (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    valF x U a ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by sorry
