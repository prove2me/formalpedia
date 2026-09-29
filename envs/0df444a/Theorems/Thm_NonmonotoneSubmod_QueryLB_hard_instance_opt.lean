-- Prove2me | Theorems.Thm_NonmonotoneSubmod_QueryLB_hard_instance_opt
-- name    : NonmonotoneSubmod.QueryLB.hard_instance_opt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:15:51.153577+00:00
-- url     : https://prove2.me/theorems/65bd6f80-afb5-48d2-bd2f-7b6eb1cc045b
-- title:
--   §4.2 — the optimum of $f_C$ is $\tfrac12 n^2(1-2\epsilon+2\epsilon^2)$, attained at $C$
-- statement:
--   Let $n$ be even, $1 \le m$, $2m \le n$, and $\epsilon = m/n$. For every $C \subseteq [n]$ with $|C| = n/2$, the maximum of the hard instance $f_C$ is
--
--   $$
--   \mathrm{OPT}(f_C) = \frac{n^2}{2} - mn + m^2 = \tfrac12 n^2 (1 - 2\epsilon + 2\epsilon^2),
--   $$
--
--   and it is attained at $S = C$ (that is, $k = n/2$, $\ell = 0$).
--
--   This is the paper's "$OPT = \tfrac12 n^2(1 - O(\epsilon))$, attained for $k = \tfrac12 n$ and $\ell = 0$", with the constant made explicit. Comparing it with the maximum $\tfrac14 n^2$ of the cut function $g$ is what gives the approximation gap of Theorem 4.5.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, pp. 1149–1150, §4.2, proof of Theorem 4.5, third bullet

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_QueryLB_HardInstance

namespace NonmonotoneSubmod.QueryLB

/-- §4.2, proof of Theorem 4.5 (pp. 1149–1150, third bullet): the maximum of `f_C` is
`OPT = ½n²(1 − 2ϵ + 2ϵ²) = n²/2 − mn + m²` (`m = ϵn`), attained at `S = C`
(`k = n/2`, `ℓ = 0`). -/
theorem hard_instance_opt (n m : ℕ) (hn : Even n) (hm : 1 ≤ m) (hmn : 2 * m ≤ n)
    (C : Finset (Fin n)) (hC : C.card = n / 2) :
    NonmonotoneSubmod.Shared.OPT (fC n m C) = (n : ℝ) ^ 2 / 2 - (m : ℝ) * n + (m : ℝ) ^ 2 ∧
      fC n m C C = NonmonotoneSubmod.Shared.OPT (fC n m C) := by sorry

end NonmonotoneSubmod.QueryLB
