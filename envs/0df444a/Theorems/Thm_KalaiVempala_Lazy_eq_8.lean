-- Prove2me | Theorems.Thm_KalaiVempala_Lazy_eq_8
-- name    : KalaiVempala.Lazy.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:22.574726+00:00
-- url     : https://prove2.me/theorems/06fc9ad0-06e2-4123-9e9b-676fb88de5eb
-- title:
--   (8), p. 304 — one FLL* update preserves the density dμ(x) ∝ e^{−ε|x|₁}
-- statement:
--   **One step of FLL\* preserves $\mu$.** Let $\varepsilon > 0$, let $\mu$ be the probability law on $\mathbb R^n$ with density $(\varepsilon/2)^n e^{-\varepsilon|x|_1}$, and let $v \in \mathbb R^n$. Suppose $p_t \sim \mu$ and $p_{t+1}$ is obtained by the update of FLL\*($\varepsilon$) with state $s_t = v$: with probability $\min\{1, d\mu(p_t - v)/d\mu(p_t)\}$ set $p_{t+1} = p_t - v$, otherwise $p_{t+1} = -p_t$. Then
--
--   $$p_{t+1} \sim \mu .$$
--
--   In the paper this is the computation that the density of $p_{t+1}$ at $x$,
--   $$d\mu(x + s_t)\min\Big\{1, \frac{d\mu(x)}{d\mu(x+s_t)}\Big\} + d\mu(-x)\Big(1 - \min\Big\{1, \frac{d\mu(-x-s_t)}{d\mu(-x)}\Big\}\Big), \tag{8}$$
--   equals $d\mu(x)$. It is the induction step showing that the perturbation of FLL\* always has law $\mu$.
--
--   **Formalization Note** The law of $p_{t+1}$ is the second marginal (`Measure.map Prod.snd`) of the joint law `fllStarJoint ε v (laplaceLaw n ε)` of $(p_t, p_{t+1})$; the statement is an equality of measures rather than of densities.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 304, display (8) and the sentence "Thus, (8) is equal to dμ(x)", proof of Lemma 1.2 (FLL* case)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Lazy_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Lazy

theorem eq_8 {n : ℕ} (ε : ℝ) (hε : 0 < ε) (v : Fin n → ℝ) :
    (fllStarJoint ε v (KalaiVempala.Multiplicative.laplaceLaw n ε)).map Prod.snd = KalaiVempala.Multiplicative.laplaceLaw n ε := by sorry

end KalaiVempala.Lazy
