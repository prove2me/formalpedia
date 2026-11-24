-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_unit_eq
-- name    : GlobalTheory.QuadraticZeta.unit_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:50.116434+00:00
-- url     : https://prove2.me/theorems/1e15e013-fbcc-4d60-b36f-2bfbe9f201da
-- title:
--   Quadratic Zeta: unit eq
-- statement:
--   The Quadratic Zeta construction uses the unit eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsBasisEmbedding.lean#L86-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsBasisEmbedding.lean#L86-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors UpperHalfPlane ComplexConjugate
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
include h2 hD
include σ

theorem GlobalTheory.QuadraticZeta.unit_eq (hd : 4 < d) (u : (𝓞 K)ˣ) : u = 1 ∨ u = -1 := by sorry
