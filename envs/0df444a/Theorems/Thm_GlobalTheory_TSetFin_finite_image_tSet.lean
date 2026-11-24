-- Prove2me | Theorems.Thm_GlobalTheory_TSetFin_finite_image_tSet
-- name    : GlobalTheory.TSetFin.finite_image_tSet
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:02:28.854671+00:00
-- url     : https://prove2.me/theorems/7664ddb9-ecf2-4c90-8128-642ef77a565e
-- title:
--   TSet Fin: finite image t Set
-- statement:
--   The TSet Fin construction uses the finite image t Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel.lean#L123-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel.lean#L123-L177

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut
noncomputable section
open GlobalTheory GlobalTheory.TSetFin
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => maximalRealSubfield L

theorem GlobalTheory.TSetFin.finite_image_tSet : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (J : Subgroup (Formalism.AUTREP.GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))),
    Formalism.L2.NG.HypOutside J χ B → ∀ (s : ReciprocityTheory.Aut.SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ),
    s.v ∉ B → Formalism.AUTREP.IsUnif L s.v ϖ →
    ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Formalism.AUTREP.tSet L n s ϖ k).Finite := by sorry
