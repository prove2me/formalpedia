-- Prove2me | Theorems.Thm_HalfIndMatch_eq_9
-- name    : HalfIndMatch.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:11:41.849228+00:00
-- url     : https://prove2.me/theorems/f0fbf405-fbab-431a-99e0-def1d9ad5268
-- title:
--   Eq. (9) — $n/L\le\frac{np}{\log C}\cdot\frac{\log(1/\kappa)}{1-\kappa}\le np$
-- statement:
--   Fix $\kappa\in(0,1)$. For all $C$ sufficiently large in terms of $\kappa$, if $C/n\le p\le1-\kappa$ then
--
--   $$\frac{n}{L}\le\frac{np}{\log C}\cdot\frac{\log(1/\kappa)}{1-\kappa}\le np.$$
--
--   It follows from $n/L=\frac{np}{\log(np)}\cdot\frac{\log b}{p}$ and the monotonicity of $x\mapsto-\log(1-x)/x$ on $(0,1)$, and it is used to bound $\log(n/s)$ in (10).
--
--   Differences from the source:
--   - reading: for C sufficiently large in terms of κ → ∃ C₀ > 1, ∀ C ≥ C₀; reason: standard reading of 'sufficiently large'
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), eq. (9), §3.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_HalfIndMatch_Lval

namespace HalfIndMatch

/-- Eq. (9), p.16: for fixed `κ ∈ (0, 1)` and all `C` sufficiently large in terms of `κ`, if
`C/n ≤ p ≤ 1 − κ` then
`n/L ≤ np/log C · log(1/κ)/(1 − κ) ≤ np`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), eq. (9), §3.2, p.16 (PDF p.18).

**Formalization Note** "For `C` sufficiently large in terms of `κ`" is `∃ C₀ > 1, ∀ C ≥ C₀`. Both
inequalities of the printed chain are stated. Real division; `n` is a natural cast to `ℝ`. -/
theorem eq_9 (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∃ C₀ : ℝ, 1 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ (n : ℕ) (p : ℝ), C / n ≤ p → p ≤ 1 - κ →
      (n : ℝ) / Lval n p ≤ (n : ℝ) * p / Real.log C * (Real.log (1 / κ) / (1 - κ)) ∧
        (n : ℝ) * p / Real.log C * (Real.log (1 / κ) / (1 - κ)) ≤ (n : ℝ) * p := by sorry

end HalfIndMatch
