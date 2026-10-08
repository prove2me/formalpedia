-- Prove2me | Theorems.Thm_NagaevLD_GenMoment_eq_2_47
-- name    : NagaevLD.GenMoment.eq_2_47
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:36.88591+00:00
-- url     : https://prove2.me/theorems/77a97462-c2cf-4625-9699-a26d75a90f65
-- title:
--   (2.47), p. 767 — for h = g′(x/n), sup_{u≥0} e^{hu−g(u)} = e^{hx/n−g(x/n)}
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ have, on $[0,\infty)$, a positive nondecreasing derivative $g'$. Let $n\ge 1$ be an integer, $x>0$, and $h=g'(x/n)$. Then the function $u\mapsto e^{hu-g(u)}$ on $u\ge 0$ attains its maximum at $u=x/n$:
--   $$\sup_{u\ge 0}e^{hu-g(u)}=e^{hx/n-g(x/n)},$$
--   and the supremum is a maximum.
--
--   With $f(u)=hu-g(u)$ one has $f'(u)=h-g'(u)$, which vanishes at $u=x/n$; this identifies the supremum appearing in (2.46).
--
--   **Formalization Note** The supremum is stated as `IsGreatest` of the image of $[0,\infty)$, which says both that the value is attained at $x/n$ and that it bounds every other value; a real `sSup` is avoided because it is $0$ on unbounded sets. The hypotheses on $g$ are imposed on $[0,\infty)$ only (including a two-sided derivative at $0$), the only region where the paper evaluates $g$; the paper's hypothesis that $g$ has a positive nondecreasing derivative implies them. The implicit $n\ge1$ of the paper is explicit in Lean.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 767, proof of Theorem 2.5, (2.47)

import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.GenMoment

/-- (2.47), p. 767: for `h = g′(x/n)` the supremum of `e^{hu - g(u)}` over `u ≥ 0` is attained
at `u = x/n` and equals `e^{hx/n - g(x/n)}`. -/
theorem eq_2_47 (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0))
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : h = g' (x / n)) :
    IsGreatest ((fun u : ℝ => Real.exp (h * u - g u)) '' Set.Ici 0)
      (Real.exp (h * (x / n) - g (x / n))) := by sorry

end NagaevLD.GenMoment
