-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_aeval_prod_snd
-- name    : GlobalTheory.UnitLemma.Desc.aeval_prod_snd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:14.505886+00:00
-- url     : https://prove2.me/theorems/6ba455c7-3bd9-4aed-9012-295c13b63c84
-- title:
--   Desc: aeval prod snd
-- statement:
--   The Desc construction uses the aeval prod snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProductLatticePositionsAndTerms.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProductLatticePositionsAndTerms.lean#L19-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProductLatticePositionsAndTerms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
variable {R A₁ A₂ : Type} [CommRing R] [CommRing A₁] [CommRing A₂] [Algebra R A₁] [Algebra R A₂]

theorem GlobalTheory.UnitLemma.Desc.aeval_prod_snd (x : A₁ × A₂) (f : R[X]) : (aeval x f).2 = aeval x.2 f := by sorry
