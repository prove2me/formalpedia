-- Prove2me | Theorems.Thm_FuchsThesis_Daroczy_eq_2_122
-- name    : FuchsThesis.Daroczy.eq_2_122
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:27.807441+00:00
-- url     : https://prove2.me/theorems/2bcfe751-012e-4c7d-b5ba-f94214d5ca76
-- title:
--   Eq. (2.122): $F(p,q)=f(p)+[p^\alpha+(1-p)^\alpha]f(q)$ is symmetric
-- statement:
--   Let $\alpha > 0$ with $\alpha \ne 1$, let $H_\alpha : \Gamma \to \mathbb R$ be symmetric and satisfy the recursion (2.111) of type $\alpha$, and let $f(x) = H_\alpha(x, 1-x)$. Define
--
--   $$
--   F(p, q) = f(p) + \big[p^{\alpha} + (1-p)^{\alpha}\big] f(q).
--   $$
--
--   Then $F$ is symmetric: $F(p, q) = F(q, p)$ for all $p, q \in [0, 1]$.
--
--   Evaluating the symmetry at $q = \tfrac12$ gives a linear equation for $f(p)$, which yields the closed formula (2.124).
--
--   Differences from the source:
--   - encoding: recursion (2.111) for every $n \ge 2$ → recursion required only when $p_1 + p_2 > 0$; reason: the right side of (2.111) is undefined at $p_1 + p_2 = 0$, so this only excludes undefined cases
--   - reading: "F(p, q) = F(q, p)" with no domain stated → for all $p, q \in [0, 1]$; reason: $f$ is defined on $[0, 1]$ (2.114), so $[0,1]^2$ is the whole domain of $F$; this is the strongest reading
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (2.122), p.33 (PDF p.42), proved in (2.125)–(2.129), pp.33–34 (PDF pp.42–43)

import Mathlib
import Definitions.Def_FuchsThesis_Daroczy_IsDist
import Definitions.Def_FuchsThesis_Daroczy_IsSymmetric
import Definitions.Def_FuchsThesis_Daroczy_SatisfiesRecursion

namespace FuchsThesis.Daroczy

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (2.122), p.33 (PDF p.42), proved through (2.125)–(2.129),
pp.33–34: for a symmetric `H_α` satisfying (2.111) and `f(x) = H_α(x, 1 − x)` (2.114), the
function `F(p, q) = f(p) + [p^α + (1 − p)^α] f(q)` is symmetric in `p` and `q`:
`F(p, q) = F(q, p)` for all `p, q ∈ [0, 1]`.

**Formalization Note.** `f` is defined on `[0, 1]` (2.114), so the symmetry is stated on the
whole square `[0, 1]²`, the domain of `F`. `f(t)` is written out as `H 2 ![t, 1 - t]`.
`α > 0, α ≠ 1` is the standing assumption of §2.4.1. -/
theorem eq_2_122 (α : ℝ) (hα : 0 < α) (hα1 : α ≠ 1) (H : (n : ℕ) → (Fin n → ℝ) → ℝ)
    (hsym : IsSymmetric H) (hrec : SatisfiesRecursion α H)
    (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    H 2 ![p, 1 - p] + (p ^ α + (1 - p) ^ α) * H 2 ![q, 1 - q]
      = H 2 ![q, 1 - q] + (q ^ α + (1 - q) ^ α) * H 2 ![p, 1 - p] := by sorry

end FuchsThesis.Daroczy
