-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFourier_le_nonzeroLocus_iff
-- name    : GlobalTheory.TorsionFourier.le_nonzeroLocus_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:08:49.566239+00:00
-- url     : https://prove2.me/theorems/8894784b-33fb-4ed3-af4b-40774714fafd
-- title:
--   Torsion Fourier: le nonzero Locus iff
-- statement:
--   The Torsion Fourier construction uses the le nonzero Locus iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PartVanishesOnTorusTorsionFourier.lean#L39-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PartVanishesOnTorusTorsionFourier.lean#L39-L55

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

theorem GlobalTheory.TorsionFourier.le_nonzeroLocus_iff {H : LB X} (s : H.Sec) (x : Sp F ⟶ X) :
    ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus s ↔ ∃ l, ⊤ ≤ x ⁻¹ᵁ H.U l ∧ valF x (H.U l) (s.f l) ≠ 0 := by sorry
