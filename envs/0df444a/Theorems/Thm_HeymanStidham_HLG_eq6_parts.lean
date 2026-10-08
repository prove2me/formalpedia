-- Prove2me | Theorems.Thm_HeymanStidham_HLG_eq6_parts
-- name    : HeymanStidham.HLG.eq6_parts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:39:31.993075+00:00
-- url     : https://prove2.me/theorems/7209a348-d05e-4827-8b83-2edc08e09fc2
-- title:
--   (6), pp. 986–987 — G = G⁺ − G⁻ and H = H⁺ − H⁻
-- statement:
--   Let $0 \le t_1 \le t_2 \le \cdots$ be arrival epochs with $t_n \to \infty$, and let the functions $f_n$ and numbers $s_n \ge 0$ satisfy (i) $f_n(t) = 0$ for $t \notin [t_n, t_n+s_n]$ and (v) $\int_0^\infty |f_n(t)|\,dt < \infty$. Suppose the customer averages $G^\pm = \lim_N \frac1N \sum_{n=1}^N g_n^\pm$ and the time averages $H^\pm = \lim_T \frac1T \int_0^T h^\pm(t)\,dt$ exist and are finite. Then $G = \lim_N \frac1N\sum_{n=1}^N g_n$ and $H = \lim_T \frac1T\int_0^T h(t)\,dt$ exist and
--
--   $$
--   G = G^+ - G^-, \qquad H = H^+ - H^-. \tag{6}
--   $$
--
--   Together with (5), $H^\pm = \lambda G^\pm$ (Theorem 1 applied to $f_n^\pm$), this gives Theorem 2.
--
--   **Formalization Note** The page prints the first identity of (6) as "$G(\omega) = G^+(\omega) - G^+(\omega)$", a misprint; the proof on p. 987 establishes $G = G^+ - G^-$, which is what is stated. The hypothesis $t_n \to \infty$ is a consequence of (2) in the paper's setting. "$H$ exists" includes integrability of $h$ on every $[0,T]$.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), pp. 986–987, proof of Theorem 2, display (6)

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open Filter Topology MeasureTheory

namespace HeymanStidham.HLG

/-- (6), pp. 986–987: under (i) and (v), with arrival epochs tending to infinity, if
`G⁺, G⁻, H⁺, H⁻` exist (finite), then `G = G⁺ − G⁻` and `H = H⁺ − H⁻` exist. -/
theorem eq6_parts (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (htinf : Tendsto t atTop atTop)
    (f : ℕ → ℝ → ℝ) (s : ℕ → ℝ) (hI : CondI t f s)
    (hv : ∀ n, IntegrableOn (f n) (Set.Ici 0))
    (Gp Gm Hp Hm : ℝ)
    (hGp : IsCustomerAverage (custTotal (posPartFn f)) Gp)
    (hGm : IsCustomerAverage (custTotal (negPartFn f)) Gm)
    (hHp : IsTimeAverage (rate (posPartFn f)) Hp)
    (hHm : IsTimeAverage (rate (negPartFn f)) Hm) :
    IsCustomerAverage (custTotal f) (Gp - Gm) ∧ IsTimeAverage (rate f) (Hp - Hm) := by sorry

end HeymanStidham.HLG
