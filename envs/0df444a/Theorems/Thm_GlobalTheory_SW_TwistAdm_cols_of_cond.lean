-- Prove2me | Theorems.Thm_GlobalTheory_SW_TwistAdm_cols_of_cond
-- name    : GlobalTheory.SW.TwistAdm.cols_of_cond
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:53.299464+00:00
-- url     : https://prove2.me/theorems/2a3d9d1c-9df9-4d76-8a4f-765564bc5ee0
-- title:
--   Twist Adm: cols of cond
-- statement:
--   The Twist Adm construction uses the cols of cond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TwistAdmissible.lean#L104-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TwistAdmissible.lean#L104-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

theorem GlobalTheory.SW.TwistAdm.cols_of_cond {R s : ℕ} {𝔛 : _root_.GlobalTheory.SW.Lt E N}
    {Λ : _root_.GlobalTheory.SW.Lt E n} {x : Matrix (Fin n) (Fin N) E}
    (hs : ∀ v ∈ _root_.GlobalTheory.SW.stdL E N, (s : E) • v ∈ 𝔛)
    (hx : ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ) :
    _root_.GlobalTheory.SW.ColsIn Λ ((R : E) • ((s : E) • x)) := by sorry
