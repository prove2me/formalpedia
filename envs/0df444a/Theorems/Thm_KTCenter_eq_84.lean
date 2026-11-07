-- Prove2me | Theorems.Thm_KTCenter_eq_84
-- name    : KTCenter.eq_84
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:44.893251+00:00
-- url     : https://prove2.me/theorems/5874d2a1-3b0e-49d6-bcb5-c50a327dfbde
-- title:
--   §6.2.1 — the Margulis–Gabber–Galil walk: spectral bound $5\sqrt2/8$ and the Hoeffding bound (84)
-- statement:
--   For every integer $m\ge2$, let $P$ be the normalized transition operator of the Margulis–Gabber–Galil graph on $\mathbb Z_m\times\mathbb Z_m$. Then:
--
--   1. $P$ is symmetric, and $\|Pf\|_2\le\frac{5\sqrt2}{8}\|f\|_2$ for every $f$ of uniform mean zero, so every nonconstant eigenvalue has absolute value at most $5\sqrt2/8<9/10$;
--   2. for every $T\ge1$, functions $g_1,\dots,g_T$ of uniform mean zero with $|g_j|\le c_j$, and every real $t$, a uniformly started walk $X_1,\dots,X_T$ with uniform transitions satisfies
--   $$\mathbb E\Bigl[\exp\Bigl(t\sum_{j=1}^Tg_j(X_j)\Bigr)\Bigr]\le\exp\Bigl(10t^2\sum_{j=1}^Tc_j^2\Bigr).\qquad(84)$$
--
--   Both are cited results in the paper ([HLW06, Construction 8.1, Theorem 8.2] and [FJS21, Theorem 1, eq. (3)]); the derandomized sampling of Theorem 6.3 rests on them.
--
--   Differences from the source:
--
--   - reading: "the explicit eight-regular multigraph from the Margulis–Gabber–Galil construction" (formula not printed) → the maps (x ± 2y, y), (x ± (2y+1), y), (x, y ± 2x), (x, y ± (2x+1)) of [HLW06, Construction 8.1]; reason: the paper cites the construction; the formula is that construction, recalled
--   - encoding: every nonconstant eigenvalue of P has |λ| ≤ 5√2/8 → P symmetric and ‖Pf‖₂² ≤ (5√2/8)²‖f‖₂² for mean-zero f; reason: equivalent for a symmetric operator whose constants are eigenvectors
--   - encoding: expectation over a uniformly started walk → uniform average over the H·8^{T−1} walk descriptions, steps 0-based; reason: Lean convention; same value
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), §6.2.1, spectral bound and eq. (84), p.61 (PDF p.63)

import Mathlib
import Definitions.Def_KTCenter_MGGWalk

namespace KTCenter

/-- **§6.2.1 spectral bound and eq. (84)**, p.61 (PDF p.63). Both are cited results in the paper,
[HLW06, Construction 8.1, Theorem 8.2] and [FJS21, Theorem 1, eq. (3)].

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** The eigenvalue statement is in its elementary form: `P` is symmetric, and
`‖Pf‖₂ ≤ (5√2/8)‖f‖₂` for every `f` of uniform mean zero, written with squared norms. The expectation
in (84) is the uniform average over walk descriptions. The formula of the graph is in `mggStep`. -/
theorem eq_84 (m : ℕ) [NeZero m] (hm : 2 ≤ m) :
    (∀ f g : ZMod m × ZMod m → ℝ, ∑ s, mggP m f s * g s = ∑ s, f s * mggP m g s) ∧
    (∀ f : ZMod m × ZMod m → ℝ, ∑ s, f s = 0 →
      ∑ s, mggP m f s ^ 2 ≤ (5 * Real.sqrt 2 / 8) ^ 2 * ∑ s, f s ^ 2) ∧
    5 * Real.sqrt 2 / 8 < 9 / 10 ∧
    ∀ (T : ℕ), 1 ≤ T → ∀ (g : Fin T → ZMod m × ZMod m → ℝ) (c : Fin T → ℝ),
      (∀ j, ∑ s, g j s = 0) → (∀ j s, |g j s| ≤ c j) → ∀ t : ℝ,
        walkAvg m T (fun X => Real.exp (t * ∑ j : Fin T, g j (X j))) ≤
          Real.exp (10 * t ^ 2 * ∑ j, c j ^ 2) := by sorry

end KTCenter
