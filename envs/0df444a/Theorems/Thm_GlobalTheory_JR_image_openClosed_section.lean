-- Prove2me | Theorems.Thm_GlobalTheory_JR_image_openClosed_section
-- name    : GlobalTheory.JR.image_openClosed_section
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:38:30.63174+00:00
-- url     : https://prove2.me/theorems/416109b3-c6b6-442b-b573-0b22eeac7c3b
-- title:
--   JR: image open Closed section
-- statement:
--   The JR construction uses the image open Closed section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvariantImageOpenClosedLocalSections.lean#L43-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvariantImageOpenClosedLocalSections.lean#L43-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsContinuousCongruenceNearSymmetricMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsCharpolyCoeffEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedMatrixInvariantSpaceExistsCompactOpenSubStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitProperOfInvertibleKrylovColumnsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOnHermitianBlockMatrixOfInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantImageOpenClosedLocalSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory.JR.ImgSec

theorem GlobalTheory.JR.image_openClosed_section : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (a₀ : Inv r F), Delta a₀ ≠ 0 → ((¬ ∃ X : Hn r F E, HasInv X a₀) → ∀ᶠ a in 𝓝 a₀, ¬ ∃ X : Hn r F E, HasInv X a) ∧ ((∃ X : Hn r F E, HasInv X a₀) → ∃ (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ ContinuousOn s Ω ∧ (∀ a ∈ Ω, Delta a ≠ 0 ∧ HasInv (s a) a) ∧ ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C}) := by sorry
