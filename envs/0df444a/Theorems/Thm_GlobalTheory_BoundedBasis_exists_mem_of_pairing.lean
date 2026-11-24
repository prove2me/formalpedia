-- Prove2me | Theorems.Thm_GlobalTheory_BoundedBasis_exists_mem_of_pairing
-- name    : GlobalTheory.BoundedBasis.exists_mem_of_pairing
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:01:59.417913+00:00
-- url     : https://prove2.me/theorems/54000539-1f98-488b-bd92-480aa755b74a
-- title:
--   Bounded Basis: exists mem of pairing
-- statement:
--   The Bounded Basis construction uses the exists mem of pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L256-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L256-L313

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)

theorem GlobalTheory.BoundedBasis.exists_mem_of_pairing {v w : Fin r → Fin r → E} (hv : ∀ i, v i ∈ X.L')
    (hw : ∀ i, w i ∈ X.L') (hvi : LinearIndependent E v) (hwi : LinearIndependent E w)
    (A : Matrix (Fin r) (Fin r) (𝓞 E)) (hvA : gramOf X.Gm v = A.map (algebraMap (𝓞 E) E))
    (hwA : gramOf X.Gm w = A.map (algebraMap (𝓞 E) E))
    (h : ∀ x : X.Λ, pairing X w hw x - pairing X v hv x ∈
      LinearMap.range (((X.NA * X.NC * X.g : ℕ) : 𝓞 E) • A).vecMulLinear) :
    ∃ γ ∈ X.Γ, ∀ i, v i = (γ : Matrix (Fin r) (Fin r) E) *ᵥ w i := by sorry
