-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_utilization_wellDefined
-- name    : KellyLossNetworks.RevisedDual.utilization_wellDefined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:08:50.857077+00:00
-- url     : https://prove2.me/theorems/3fcb4d12-0770-40d7-9ea4-7819a548ec3c
-- title:
--   §3.1, (3.4) — the implicit relation defines U : ℝ₊ × ℤ₊ → ℝ₊
-- statement:
--   Let $C\ge1$ be an integer and $E(\nu,C)$ Erlang's formula. As the offered load $\nu$ increases from $0$ to $\infty$, the quantity $-\log(1-E(\nu,C))$ increases from $0$ to $\infty$: the map
--   $$\nu\longmapsto -\log\big(1-E(\nu,C)\big)$$
--   is strictly increasing and continuous on $[0,\infty)$ and maps $[0,\infty)$ bijectively onto $[0,\infty)$. Consequently the utilization function $U$ satisfies the implicit relation (3.4),
--   $$U\big(-\log(1-E(\nu,C)),\,C\big)=\nu\,\big(1-E(\nu,C)\big)\qquad\text{for every }\nu\ge0,$$
--   and $U(y,C)\ge0$ for every $y\ge0$.
--
--   This is what makes $U$ a well-defined function on $\mathbb R_+\times\{C\ge1\}$, the input to the revised dual problem (3.5).
--
--   **Formalization Note** The paper writes $U:\mathbb R_+\times\mathbb Z_+\to\mathbb R_+$. At $C=0$ Erlang's formula is identically $1$ and the left side of (3.4) is $-\log 0$, so $C\in\mathbb Z_+$ is read as $C\ge1$.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 338, §3.1, (3.4) and the sentence after it

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyLossNetworks_RevisedDual_Problem

namespace KellyLossNetworks.RevisedDual

/-- **(3.4) defines a function `U : ℝ₊ × ℤ₊ → ℝ₊`.** For `C ≥ 1`, as `ν` increases from `0` to
`∞` the first argument `−log(1 − E(ν, C))` of `U` in (3.4) increases from `0` to `∞`: the map
`ν ↦ −log(1 − E(ν, C))` is strictly increasing, continuous, and a bijection of `[0, ∞)` onto
`[0, ∞)`. Consequently the function `U` satisfies the implicit relation (3.4),
`U(−log(1 − E(ν, C)), C) = ν(1 − E(ν, C))` for every `ν ≥ 0`, and `U(y, C) ≥ 0` for `y ≥ 0`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 338, §3.1, the sentence after (3.4) (unnumbered).

**Formalization Note.** The paper writes `U : ℝ₊ × ℤ₊ → ℝ₊`; at `C = 0` the left side of (3.4)
is `−log 0` (Erlang's formula is `E(ν, 0) = 1`), so `C ∈ ℤ₊` is read as `C ≥ 1`. -/
theorem utilization_wellDefined (C : ℕ) (hC : 1 ≤ C) :
    StrictMonoOn (fun ν : ℝ => -Real.log (1 - KellyStochasticNetworks.erlang ν C)) (Set.Ici 0) ∧
    ContinuousOn (fun ν : ℝ => -Real.log (1 - KellyStochasticNetworks.erlang ν C)) (Set.Ici 0) ∧
    Set.BijOn (fun ν : ℝ => -Real.log (1 - KellyStochasticNetworks.erlang ν C))
      (Set.Ici 0) (Set.Ici 0) ∧
    (∀ ν : ℝ, 0 ≤ ν →
      U (-Real.log (1 - KellyStochasticNetworks.erlang ν C)) C
        = ν * (1 - KellyStochasticNetworks.erlang ν C)) ∧
    (∀ y : ℝ, 0 ≤ y → 0 ≤ U y C) := by sorry

end KellyLossNetworks.RevisedDual
