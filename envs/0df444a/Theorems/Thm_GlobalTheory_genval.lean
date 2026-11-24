-- Prove2me | Theorems.Thm_GlobalTheory_genval
-- name    : GlobalTheory.genval
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:54:18.237603+00:00
-- url     : https://prove2.me/theorems/e682f59e-f8d5-449b-a649-d4102a39f368
-- title:
--   Global Theory: genval
-- statement:
--   The Global Theory construction uses the genval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAlgClosedTranscendentalSpecialisingEverywh.lean#L58-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAlgClosedTranscendentalSpecialisingEverywh.lean#L58-L135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAlgClosedTranscendentalSpecialisingEverywh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing
open GlobalTheory

theorem GlobalTheory.genval (K : Type) [Field K] [IsAlgClosed K] : ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) ∧ ∀ a : K, ∃ (V : ValuationSubring L) (ιV : K →+* V) (r : V →+* K) (sV : V), (algebraMap V L).comp ιV = ι ∧ r.comp ιV = RingHom.id K ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ algebraMap V L sV = s ∧ r sV = a := by sorry
