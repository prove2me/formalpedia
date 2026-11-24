-- Prove2me | Theorems.Thm_GlobalTheory_MaxOrder_isIntegral_aeval_eq_aeval_map
-- name    : GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:21:10.784325+00:00
-- url     : https://prove2.me/theorems/16656f94-5aa0-42bb-b006-407aec703a2f
-- title:
--   Max Order: is Integral aeval eq aeval map
-- statement:
--   The Max Order construction uses the is Integral aeval eq aeval map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralAevalEqAevalMapOfCoprimeCharpoly.lean#L74-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralAevalEqAevalMapOfCoprimeCharpoly.lean#L74-L100

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharpolyEqPowOfIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Matrix GlobalTheory.LatOrb IsLocalRing
open GlobalTheory GlobalTheory.MaxOrder

theorem GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ p : K[X], IsIntegral O (aeval γ p) → ∃ r : O[X], aeval γ p = aeval γ (r.map (algebraMap O K)) := by sorry
