-- Prove2me | Theorems.Thm_GlobalTheory_T_unramified_quadratic_order_principal
-- name    : GlobalTheory.T.unramified_quadratic_order_principal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:40:18.565179+00:00
-- url     : https://prove2.me/theorems/247b802a-05fa-57b3-bdb6-4a4ad4274ddc
-- title:
--   T: unramified quadratic order principal
-- statement:
--   The T construction uses the unramified quadratic order principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuadraticOrderPrincipalStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuadraticOrderPrincipalStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuadraticOrderPrincipal
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuadraticOrderPrincipalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unramified_quadratic_order_principal : ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R] [CommRing O] (ι : R →+* O) (δ : O) (D : R), δ * δ = ι D → (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) → IsUnit D → IsUnit (2 : R) → (¬ ∃ e : R, D = e * e) → IsPrincipalIdealRing O := by sorry
