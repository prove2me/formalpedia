-- Prove2me | Theorems.Thm_MultiSecretary_BR_br_ratio_jump
-- name    : MultiSecretary.BR.br_ratio_jump
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:18:41.039332+00:00
-- url     : https://prove2.me/theorems/f2a5671e-9c03-4216-a0dd-dac6069ae352
-- title:
--   Sec. 4, p. 13 — for $t\le n-2\delta^{-1}-1$ the BR budget ratio jumps by at most $\delta/2$
-- statement:
--   Under the Budget-Ratio policy with $(n,k)\in\mathcal T$, fix $0<\delta<\epsilon=\tfrac12\min_j f_j$. For every $t\le n-2\delta^{-1}-1$,
--   $$\Big|\frac{K_t}{n-t}-\frac{K_{t+1}}{n-(t+1)}\Big|\le\frac\delta2.$$
--
--   Hence the budget ratio cannot jump over the $\delta/2$-neighbourhood of a threshold before the cut-off time, so on $\{\tau_0<n-2\delta^{-1}-1\}$ the threshold $T_{j(\tau_0)}$ it first approaches is $T_j$ or $T_{j+1}$, where $k/n\in[T_j,T_{j+1})$.
--
--   **Formalization Note** The hypothesis $\delta<\epsilon$ is the standing choice of p. 13.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Sec. 4, p. 13

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model
import Definitions.Def_MultiSecretary_BR_Policy

namespace MultiSecretary.BR

/-- Sec. 4, p. 13: fix `0 < δ < ϵ`. For all `t ≤ n − 2δ⁻¹ − 1` the jumps of the BR budget ratio
satisfy `|K_t/(n − t) − K_{t+1}/(n − (t + 1))| ≤ δ/2`. -/
theorem br_ratio_jump {m : ℕ} (I : Instance m) (n k : ℕ) (hk : k ≤ n) (δ : ℝ) (hδ : 0 < δ)
    (hδε : δ < I.eps) (x : Fin n → Fin m) (t : ℕ) (ht : (t : ℝ) ≤ (n : ℝ) - 2 / δ - 1) :
    |I.ratio n k x t - I.ratio n k x (t + 1)| ≤ δ / 2 := by sorry

end MultiSecretary.BR
