-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_isIntegral_of_basicOpen
-- name    : GlobalTheory.PrimeSection.isIntegral_of_basicOpen
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:43:28.128752+00:00
-- url     : https://prove2.me/theorems/cd270e75-b8bc-46f0-8200-e43ccc1756b4
-- title:
--   Prime Section: is Integral of basic Open
-- statement:
--   The Prime Section construction uses the is Integral of basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L170-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L170-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection

theorem GlobalTheory.PrimeSection.isIntegral_of_basicOpen {X Y : Scheme.{u}} {t : Γ(X, ⊤)}
    (ht : ∀ U : X.Opens, IsAffineOpen U →
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t ∈ nonZeroDivisors Γ(X, U))
    (j : Y ⟶ X) [IsOpenImmersion j] [IsIntegral Y] (hj : j.opensRange = X.basicOpen t) :
    IsIntegral X := by sorry
