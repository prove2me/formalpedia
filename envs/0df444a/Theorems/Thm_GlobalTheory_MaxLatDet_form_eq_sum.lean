-- Prove2me | Theorems.Thm_GlobalTheory_MaxLatDet_form_eq_sum
-- name    : GlobalTheory.MaxLatDet.form_eq_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:09:34.467094+00:00
-- url     : https://prove2.me/theorems/844b614b-7c90-570d-bee6-17b2ed693aad
-- title:
--   Max Lat Det: form eq sum
-- statement:
--   The Max Lat Det construction uses the form eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeBadPrimesIffGramDet.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeBadPrimesIffGramDet.lean#L17-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.MaxLatDet
open IsDedekindDomain
variable {K V ι : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]

theorem GlobalTheory.MaxLatDet.form_eq_sum (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Module.Basis ι K V)
    (he : ∀ i l, i ≠ l → h (e i) (e l) = 0) (x y : V) :
    h x y = ∑ i, star (e.repr x i) * h (e i) (e i) * e.repr y i := by sorry
