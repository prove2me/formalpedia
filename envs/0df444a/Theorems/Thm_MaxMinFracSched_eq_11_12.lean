-- Prove2me | Theorems.Thm_MaxMinFracSched_eq_11_12
-- name    : MaxMinFracSched.eq_11_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:29.694536+00:00
-- url     : https://prove2.me/theorems/38889666-32bd-4dfa-877e-931519adae85
-- title:
--   Eqs. (11)–(12) — work due at $t_i$: $D_1=x^{k-1}$, $D_i=t_i(1-x^2)/x^{i-1}$ (corrected: display (10))
-- statement:
--   Let $k\ge1$, $0<x<1$, and let $D_i=\sum_{m=0}^{i-1}w_m(i)$ be the total work due at $t_i$ in the hard family. Then
--   $$D_1=x^{k-1}\quad(11),\qquad D_i=t_i\cdot\frac{1-x^2}{x^{i-1}}\quad(2\le i\le k)\quad(12).$$
--
--   These counts feed the work bound (13): an algorithm that is $\alpha$-competitive on every prefix must do at least $\alpha x^{i-1}D_i$ work on the jobs due at $t_i$.
--
--   Differences from the source:
--   - correction: display (10) as printed → the corrected works w_m(j) (see Lemma 6.2's correction); reason: as printed, (10) puts the release at t_0 under its second and third cases, so k = 2, x = 1/3 (t = (0, 1/3, 1), T_1 = 1/3) give D_1 = w_0(1) = (1−x)/x · T_1 = 2/3 ≠ x^{k−1} = 1/3; even with w_0(j) = T_j from the sentence on p.29, the printed case i = 1 gives w_1(2) = T_2, and k = 3, x = 1/2 give D_2 = T_2 + T_2 = 1/2 ≠ t_2(1 − x²)/x = 3/4; the page's own computation of D_i (p.31, which uses (1−x)T_i/x^j for j ≥ 1) uses the corrected family
--   - encoding: D_i = Σ_{j=0}^{i−1} w_j(i) → Dtot x k i = Σ_{m ∈ range i} hw x k m i; reason: same sum
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 6.3, Eqs. (11)–(12), pp.31–32 (PDF pp.33–34)

import Mathlib
import Definitions.Def_MaxMinFracSched_tt
import Definitions.Def_MaxMinFracSched_Dtot

namespace MaxMinFracSched

/-- **Section 6.3, (11)–(12): the work due at each deadline.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 6.3, pp.31–32
(PDF pp.33–34): "When i = 1, the amount of work due at t1 is exactly D1 = T1 = t1 − 0 = x^{k−1}.
(11) For all i > 1, this sum telescopes. Recalling that Ti = ti(1 − x), … = ti · (1 − x²)/x^{i−1}.
(12)"

**Formalization Note.** `D_i` is the total work due at `t_i` in the corrected family (`Dtot`).
Parameters `k ≥ 1`, `0 < x < 1`; (12) for `2 ≤ i ≤ k`. -/
theorem eq_11_12 (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Dtot x k 1 = x ^ (k - 1) ∧
    ∀ i : ℕ, 2 ≤ i → i ≤ k → Dtot x k i = tt x k i * (1 - x ^ 2) / x ^ (i - 1) := by sorry

end MaxMinFracSched
