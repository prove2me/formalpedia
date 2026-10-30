-- Prove2me | Theorems.Thm_JuschenkoMonod_tendsto_innerRatio_and_tendsto_l2Norm_restrictZero_div
-- name    : JuschenkoMonod.tendsto_innerRatio_and_tendsto_l2Norm_restrictZero_div
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:24:46.623799+00:00
-- url     : https://prove2.me/theorems/f9fb653c-cb93-493f-8460-a6b744421011
-- title:
--   Theorem 2.1 — ⟨g(f_n), f_n⟩/‖f_n‖² → 1 for g ∈ W(ℤ), and ‖f_n|_{x₀=0}‖/‖f_n‖ → 1
-- statement:
--   Let $f_n(x) = \exp\big(-n\sum_{j\in\mathbf Z}x_je^{-|j|/n}\big)$ on $\{0,1\}^{\mathbf Z}$ with the symmetric Bernoulli measure. For every $g \in W(\mathbf Z)$, as $n \to \infty$:
--   - $\langle g(f_n), f_n\rangle/\|f_n\|^2 \to 1$, where $g(f_n)(x) = f_n(g^{-1}x)$ with $(g^{-1}x)_j = x_{g(j)}$, and the inner product and norm are those of $L^2$;
--   - $\|f_n|_{x_0=0}\|/\|f_n\| \to 1$, where $f_n|_{x_0=0}$ is $f_n$ multiplied by the indicator function of the cylinder $\{x : x_0 = 0\}$.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 777, Theorem 2.1

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem tendsto_innerRatio_and_tendsto_l2Norm_restrictZero_div (g : Equiv.Perm ℤ)
    (hg : g ∈ IntervalExchange.wobbling ℤ) :
    Filter.Tendsto (fun n => innerRatio g n) Filter.atTop (nhds 1) ∧
      Filter.Tendsto (fun n => l2Norm (restrictZero 0 (fn n)) / l2Norm (fn n)) Filter.atTop
        (nhds 1) := by
  sorry

end JuschenkoMonod
