-- Prove2me | Theorems.Thm_GlobalTheory_T_split_quadratic_order_principal
-- name    : GlobalTheory.T.split_quadratic_order_principal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:44.997465+00:00
-- url     : https://prove2.me/theorems/adb3cd56-2a54-5ec9-ab9a-52bc1868e104
-- title:
--   T: split quadratic order principal
-- statement:
--   The T construction uses the split quadratic order principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SplitQuadraticOrderPrincipalStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SplitQuadraticOrderPrincipalStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitQuadraticOrderPrincipal
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitQuadraticOrderPrincipalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.split_quadratic_order_principal : ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O] (ι : R →+* O) (δ : O) (e : R), δ * δ = ι (e * e) → (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) → IsUnit e → IsUnit (2 : R) → IsPrincipalIdealRing O := by sorry
