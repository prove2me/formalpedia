-- Prove2me | Theorems.Thm_GlobalTheory_etale_mvPolynomial_map_of_etale
-- name    : GlobalTheory.etale_mvPolynomial_map_of_etale
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:18:44.720705+00:00
-- url     : https://prove2.me/theorems/ea95ddd4-02ab-42a6-a994-410fa644205e
-- title:
--   Global Theory: etale mv Polynomial map of etale
-- statement:
--   The Global Theory construction uses the etale mv Polynomial map of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtalePolynomialSubstitution.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtalePolynomialSubstitution.lean#L7-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtalePolynomialSubstitution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial

theorem GlobalTheory.etale_mvPolynomial_map_of_etale {B A N : Type} [CommRing B] [CommRing A] (g : B →+* A)
    (hg : g.Etale) : (MvPolynomial.map (σ := N) g).Etale := by sorry
