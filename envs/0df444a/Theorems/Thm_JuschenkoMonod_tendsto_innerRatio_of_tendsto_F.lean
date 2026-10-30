-- Prove2me | Theorems.Thm_JuschenkoMonod_tendsto_innerRatio_of_tendsto_F
-- name    : JuschenkoMonod.tendsto_innerRatio_of_tendsto_F
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:23:39.621084+00:00
-- url     : https://prove2.me/theorems/e320bd2d-23b3-4e92-b062-c1f7bbf509e3
-- title:
--   Proposition 2.2 — ⟨g(f_n), f_n⟩/‖f_n‖² → 1 provided F_n(g) → 0
-- statement:
--   Let $g \in W(\mathbf Z)$, and suppose that $F_n(g) \to 0$ as $n \to \infty$, where $$F_n(g) = \sum_{j\in\mathbf Z}\frac{a_{n,j}^2}{1 + a_{n,j}^2}\,e^{-|j|/n}\big(|g(j)| - |j|\big), \qquad a_{n,j} = \exp(-ne^{-|j|/n}).$$ Then $\langle g(f_n), f_n\rangle/\|f_n\|^2 \to 1$ as $n \to \infty$. Here $f_n(x) = \exp\big(-n\sum_{j\in\mathbf Z}x_je^{-|j|/n}\big)$ on $\{0,1\}^{\mathbf Z}$ with the symmetric Bernoulli measure, $g(f_n)(x) = f_n(g^{-1}x)$ with $(g^{-1}x)_j = x_{g(j)}$, and the inner product and norm are those of $L^2$.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 778, Proposition 2.2

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem tendsto_innerRatio_of_tendsto_F (g : Equiv.Perm ℤ) (hg : g ∈ IntervalExchange.wobbling ℤ)
    (hF : Filter.Tendsto (fun n => F n g) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => innerRatio g n) Filter.atTop (nhds 1) := by
  sorry

end JuschenkoMonod
