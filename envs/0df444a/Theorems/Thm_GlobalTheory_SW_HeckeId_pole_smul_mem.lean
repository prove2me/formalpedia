-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeckeId_pole_smul_mem
-- name    : GlobalTheory.SW.HeckeId.pole_smul_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:41:09.751372+00:00
-- url     : https://prove2.me/theorems/85fb274e-830d-4997-ab1d-458a17f1a2b3
-- title:
--   Hecke Id: pole smul mem
-- statement:
--   The Hecke Id construction uses the pole smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean#L250-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean#L250-L267

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
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
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
omit [IsCMField E]

theorem GlobalTheory.SW.HeckeId.pole_smul_mem {P : Ideal (𝓞 E)} [hP : P.IsMaximal] {t : E}
    (ht : ∀ c ∈ P, IsIntegral ℤ ((c : E) * t)) {d r : 𝓞 E} (hd : d ∈ P) (hr : r ∉ P)
    (e : (r : E) = (d : E) * t) (L : Lt E n) (v : L) :
    t • (v : Fin n → E) ∈ L ↔ v ∈ (P • ⊤ : Submodule (𝓞 E) L) := by sorry
