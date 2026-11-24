-- Prove2me | Theorems.Thm_GlobalTheory_Ex_SymLift_normalising_factor
-- name    : GlobalTheory.Ex.SymLift.normalising_factor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:06:34.324612+00:00
-- url     : https://prove2.me/theorems/c33c6c2d-26a0-408c-921b-66feaf06bb20
-- title:
--   Sym Lift: normalising factor
-- statement:
--   The Sym Lift construction uses the normalising factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormalisingFactor.lean#L148-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormalisingFactor.lean#L148-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.SymLift
variable {O : Type} [CommRing O] (N : NumD O)

theorem GlobalTheory.Ex.SymLift.normalising_factor : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ), Odd k → ∀ p p' : N.QT k, (∀ w : Oˣ, w = N.wQ p ↔ (w ^ 2 * dbl N.θ N.σ p.1.2.b ^ k = N.tk p p ∧ w ^ k = N.ψ p.1.1.toAdd * mulq N.θ N.σ k p.1.2.b)) ∧ N.wQ p * N.wQ p' * N.tk p p' = N.wp p p' ^ ((k + 1) / 2) * N.wQ (p * p') ∧ N.wQ p⁻¹ * N.σ p.1.2.b ^ k = N.wQ p := by sorry
