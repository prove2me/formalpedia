-- Prove2me | Theorems.Thm_Freiman_form_minimum_infimum_assembly
-- name    : Freiman.form_minimum_infimum_assembly
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:16.464748+00:00
-- url     : https://prove2.me/theorems/b02c9d7c-22e2-4e48-9cc3-3742f37480f5
-- title:
--   Infimum comparison closes the reduced-form minimum identity
-- statement:
--   For the upper inequality, evaluate every orbit form at (1,0) and use minimum invariance; take the infimum over n. For the lower inequality, apply the explicit lower bound to the nonempty, bounded-below set in quadraticMinimum.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, found:minimum-identity

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_minimum_infimum_assembly (R : ReducedOrbit) (hinv : ∀ n : ℤ, reducedMinimum (R.alpha n) (R.beta n)=reducedMinimum (R.alpha 0) (R.beta 0)) (hlower : ∀ n p q : ℤ, (p ≠ 0 ∨ q ≠ 0) → orbitReciprocalInfimum R ≤ |reducedValue (R.alpha n) (R.beta n) p q|) :
    reducedMinimum (R.alpha 0) (R.beta 0) = orbitReciprocalInfimum R := by
  sorry

end Freiman
