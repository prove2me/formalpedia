-- Prove2me | Theorems.Thm_NOFSeparation750_CodedGIP_generic_multitape_encoder_of_generator
-- name    : NOFSeparation750.CodedGIP.generic_multitape_encoder_of_generator
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:46:31.442842+00:00
-- url     : https://prove2.me/theorems/af246909-e198-40d3-973b-fd45c9379c8f
-- title:
--   Polynomial-time multi-tape encoding from generated matrices
-- statement:
--   Let $D$ be a presented family of $(6/2^a,3/4)$-compatible code pairs over a fixed finite field, and suppose a deterministic multi-tape machine generates its two matrices at level $j$ within $p(r_j)$ steps. Then there is one deterministic multi-tape machine which, on the level, a small/large selector, and a coefficient vector, outputs the corresponding codeword. A single enlarged polynomial bounds both generation and encoding on all valid inputs.
--
--   The encoder parses the unary dimension headers and row-major field symbols, multiplies the selected matrix by the coefficient vector using finite-field arithmetic, and serializes the result. Compatibility supplies $\dim V_j\ge 6r_j/2^a$, so the valid message length controls $r_j$ linearly; this is what makes the composition polynomial in $r_j$ even though the level itself is written in unary.
--
--   **Formalization Note.** The space bounds are unrestricted existential functions, as in the source's time-only effectiveness assertion. The enlarged polynomial also dominates the original generator clock.
-- source:
--   Wang–Wang–Wu, STOC 2027 submission #750, Appendix A.3 p.13, Computation paragraph: “Encoding multiplies the basis coefficients by this matrix”; generic algorithmic formalization of that assertion with the dimension lower bound from Definition 3.1 p.7.

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_EffectiveCodes
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List

namespace NOFSeparation750.CodedGIP

/-- A generator matrix in the standard binary layout determines a polynomial-time
multi-tape encoder. Compatibility makes the valid message length linear in the
code length, so the composed generator/encoder has polynomial weighted cost. -/
theorem generic_multitape_encoder_of_generator {k a : ℕ} (F : Type) [Field F] [Fintype F]
    (D : PairFamily F a) (codec : (Fin (2 * a) → Bool) ≃ F)
    (hcomp : ∀ j, Compatible (D j).small.code (D j).large.code k
      (6 / (2 ^ a : ℝ)) (3 / 4))
    (gen : List Bool → List Bool) (tg sg : List Bool → ℕ) (p : Polynomial ℕ)
    (hgen : Turing.MultiTapeTM.ComputableInTimeAndSpace gen Turing.MultiTapeTM.encBits
      Turing.MultiTapeTM.encBits tg sg)
    (hgspec : ∀ j, gen (unary j) = generatorBits codec (D j).small ++
      generatorBits codec (D j).large ∧ tg (unary j) ≤ p.eval (codeLength a j)) :
    ∃ (enc : List Bool → List Bool) (te se : List Bool → ℕ) (p' : Polynomial ℕ),
      Turing.MultiTapeTM.ComputableInTimeAndSpace enc Turing.MultiTapeTM.encBits
        Turing.MultiTapeTM.encBits te se ∧
      (∀ j, tg (unary j) ≤ p'.eval (codeLength a j)) ∧
      ∀ j,
        (∀ u : Fin (D j).small.dimension → F,
          enc (unary j ++ [false] ++ fieldVectorBits codec u) =
            fieldVectorBits codec ((D j).small.encode u).val ∧
          te (unary j ++ [false] ++ fieldVectorBits codec u) ≤ p'.eval (codeLength a j)) ∧
        (∀ u : Fin (D j).large.dimension → F,
          enc (unary j ++ [true] ++ fieldVectorBits codec u) =
            fieldVectorBits codec ((D j).large.encode u).val ∧
          te (unary j ++ [true] ++ fieldVectorBits codec u) ≤ p'.eval (codeLength a j)) := by sorry
