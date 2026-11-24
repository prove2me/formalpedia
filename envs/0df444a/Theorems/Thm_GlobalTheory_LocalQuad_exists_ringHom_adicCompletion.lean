-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_exists_ringHom_adicCompletion
-- name    : GlobalTheory.LocalQuad.exists_ringHom_adicCompletion
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:13:50.193682+00:00
-- url     : https://prove2.me/theorems/5a685092-9c1f-4f3c-9a15-4f5aa64052ca
-- title:
--   Local Quad: exists ring Hom adic Completion
-- statement:
--   The Local Quad construction uses the exists ring Hom adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRingHomAdicCompletion.lean#L6-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRingHomAdicCompletion.lean#L6-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero

theorem GlobalTheory.LocalQuad.exists_ringHom_adicCompletion (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (w : HeightOneSpectrum (𝓞 L)) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (φ : v.adicCompletion K →+* w.adicCompletion L),
      ∀ x : K, φ (algebraMap K (v.adicCompletion K) x) =
        algebraMap L (w.adicCompletion L) (algebraMap K L x) := by sorry
