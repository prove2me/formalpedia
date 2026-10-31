-- Prove2me | Theorems.Thm_FuchsThesis_Daroczy_eq_2_124
-- name    : FuchsThesis.Daroczy.eq_2_124
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:25.137825+00:00
-- url     : https://prove2.me/theorems/11c71b1d-664d-4a6d-8ca9-f91a3ac6cea8
-- title:
--   Eq. (2.124): $f(p)=C(2^{1-\alpha}-1)^{-1}[p^\alpha+(1-p)^\alpha-1]$
-- statement:
--   Let $\alpha > 0$ with $\alpha \ne 1$, let $H_\alpha : \Gamma \to \mathbb R$ be symmetric and satisfy the recursion (2.111) of type $\alpha$, and let $f(x) = H_\alpha(x, 1-x)$. Then for every $p \in [0, 1]$
--
--   $$
--   f(p) = C\,\big(2^{1-\alpha} - 1\big)^{-1} \big[p^{\alpha} + (1-p)^{\alpha} - 1\big], \qquad C = f\!\left(\tfrac12\right) = H_\alpha\!\left(\tfrac12, \tfrac12\right).
--   $$
--
--   The binary information function is thus determined by its value at the uniform distribution; with (2.115) this determines $H_\alpha$ on all of $\Gamma$.
--
--   **Formalization Note** Powers are real powers, so $0^\alpha = 0$ for $\alpha > 0$; $2^{1-\alpha} - 1 \ne 0$ because $\alpha \ne 1$.
--
--   Differences from the source:
--   - encoding: recursion (2.111) for every $n \ge 2$ → recursion required only when $p_1 + p_2 > 0$; reason: the right side of (2.111) is undefined at $p_1 + p_2 = 0$, so this only excludes undefined cases
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (2.124), p.33 (PDF p.42)

import Mathlib
import Definitions.Def_FuchsThesis_Daroczy_IsDist
import Definitions.Def_FuchsThesis_Daroczy_IsSymmetric
import Definitions.Def_FuchsThesis_Daroczy_SatisfiesRecursion

namespace FuchsThesis.Daroczy

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (2.124), p.33 (PDF p.42), in the proof of Theorem 2.7: for a
symmetric `H_α` satisfying (2.111) and `f(x) = H_α(x, 1 − x)` (2.114),
`f(p) = C (2^{1−α} − 1)^{−1} [p^α + (1 − p)^α − 1]` for every `p ∈ [0, 1]`,
where `C = f(1/2)` ("Eq. (2.124) also holds for p = 0 and p = 1").

**Formalization Note.** `C = f(1/2) = H_α(1/2, 1/2)` is written out; powers are `Real.rpow`, so
`0 ^ α = 0` for `α > 0`. `2^{1−α} − 1 ≠ 0` because `α ≠ 1`. `α > 0, α ≠ 1` is the standing
assumption of §2.4.1. -/
theorem eq_2_124 (α : ℝ) (hα : 0 < α) (hα1 : α ≠ 1) (H : (n : ℕ) → (Fin n → ℝ) → ℝ)
    (hsym : IsSymmetric H) (hrec : SatisfiesRecursion α H)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    H 2 ![p, 1 - p] = H 2 ![1 / 2, 1 - 1 / 2] * ((2 : ℝ) ^ (1 - α) - 1)⁻¹ *
      (p ^ α + (1 - p) ^ α - 1) := by sorry

end FuchsThesis.Daroczy
