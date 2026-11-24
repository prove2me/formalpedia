-- Prove2me | Theorems.Thm_GlobalTheory_HenselZero_formallySmooth_quotient
-- name    : GlobalTheory.HenselZero.formallySmooth_quotient
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:20:34.189817+00:00
-- url     : https://prove2.me/theorems/ccca8f8f-d14a-49c9-aedd-af4798e335c2
-- title:
--   Hensel Zero: formally Smooth quotient
-- statement:
--   The Hensel Zero construction uses the formally Smooth quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FormallySmoothQuotient.lean#L9-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FormallySmoothQuotient.lean#L9-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FormallySmoothQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HenselZero
open IsLocalRing GlobalTheory.SqZero

theorem GlobalTheory.HenselZero.formallySmooth_quotient {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    [Fintype ι] [DecidableEq ι] (f : ι → S) (τ : ι → Derivation R S S)
    (h : IsUnit (Matrix.of fun i k => τ k (f i)).det) :
    Algebra.FormallySmooth R (S ⧸ Ideal.span (Set.range f)) := by sorry
