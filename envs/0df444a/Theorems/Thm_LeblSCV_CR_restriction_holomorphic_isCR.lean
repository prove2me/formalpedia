-- Prove2me | Theorems.Thm_LeblSCV_CR_restriction_holomorphic_isCR
-- name    : LeblSCV.CR.restriction_holomorphic_isCR
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:58:52.041983+00:00
-- url     : https://prove2.me/theorems/ebb3d8c8-7f82-4883-928f-97229d4dff08
-- title:
--   Proposition 3.2.6 — restrictions of holomorphic functions are CR functions
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open and let $M \subset U$ be a smooth (respectively real-analytic) real hypersurface. If $F : U \to \mathbb{C}$ is holomorphic, then the restriction
--   $$f = F|_M$$
--   is a smooth (respectively real-analytic) CR function on $M$. Both readings are asserted. Severi's theorem (Theorem 3.2.9) is the local converse in the real-analytic case.
--
--   **Formalization Note.** Holomorphic is `DifferentiableOn ℂ F U`; the restriction is $F$ itself viewed through `IsSmoothCRFunction M F` / `IsRealAnalyticCRFunction M F`, whose conditions only read $F$ on $M$. The two cases are the two conjuncts: smooth hypersurface ⇒ smooth CR function, real-analytic hypersurface (Definition 3.1.9) ⇒ real-analytic CR function.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 111, Proposition 3.2.6

import Mathlib
import Definitions.Def_LeblSCV_CR_IsRealAnalyticHypersurface
import Definitions.Def_LeblSCV_CR_IsSmoothCRFunction

namespace LeblSCV.CR

/-- Proposition 3.2.6 (Lebl, p. 111): let `M ⊂ U` be a smooth (resp. real-analytic) real
hypersurface in an open `U ⊂ ℂⁿ`. If `F : U → ℂ` is holomorphic, then the restriction
`f = F|_M` is a smooth (resp. real-analytic) CR function. Both readings are stated. -/
theorem restriction_holomorphic_isCR {n : ℕ} (U M : Set (Fin n → ℂ)) (hU : IsOpen U)
    (hMU : M ⊆ U) (F : (Fin n → ℂ) → ℂ) (hF : DifferentiableOn ℂ F U) :
    (IsSmoothHypersurface M → IsSmoothCRFunction M F) ∧
      (IsRealAnalyticHypersurface M → IsRealAnalyticCRFunction M F) := by sorry

end LeblSCV.CR
