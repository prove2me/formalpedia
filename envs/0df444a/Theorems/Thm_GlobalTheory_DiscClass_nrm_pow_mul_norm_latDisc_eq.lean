-- Prove2me | Theorems.Thm_GlobalTheory_DiscClass_nrm_pow_mul_norm_latDisc_eq
-- name    : GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:07.610197+00:00
-- url     : https://prove2.me/theorems/a992dd69-dcf1-4dec-801e-b9367c768cdd
-- title:
--   Disc Class: nrm pow mul norm lat Disc eq
-- statement:
--   The Disc Class construction uses the nrm pow mul norm lat Disc eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FractionalIdealNormPowSixMulDiscriminantClassInv.lean#L48-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FractionalIdealNormPowSixMulDiscriminantClassInv.lean#L48-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FractionalIdealNormPowSixMulDiscriminantClassInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DiscClass

theorem GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (h2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λa Λb : PeriodPair)
    (ha : IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λa) (hb : IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λb)
    (hcl : ClassGroup.mk K 𝔞 = ClassGroup.mk K 𝔟) :
    nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λa‖ = nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λb‖ := by sorry
