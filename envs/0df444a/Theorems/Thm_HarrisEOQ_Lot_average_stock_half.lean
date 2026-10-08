-- Prove2me | Theorems.Thm_HarrisEOQ_Lot_average_stock_half
-- name    : HarrisEOQ.Lot.average_stock_half
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:20:07.314836+00:00
-- url     : https://prove2.me/theorems/bf0e52f0-f4dc-4466-9cd1-a44331948985
-- title:
--   p. 948 — under regular movement the long-run average stock is X/2
-- statement:
--   Let $M > 0$ be the number of units used per month and $X > 0$ the lot size. Under regular movement the stock on hand at time $t \ge 0$ (months) is the sawtooth $\operatorname{stock}(t) = X(1 - \{Mt/X\})$: it starts at $X$, is used up at rate $M$, and is replenished by a lot of $X$ each time it reaches nothing. Then the long-run time average of the stock is half the lot size:
--   $$
--   \lim_{T \to \infty} \frac1T \int_0^T \operatorname{stock}(t)\,dt = \frac{X}{2}.
--   $$
--
--   This is the first step of Harris's derivation: the interest charge is levied on the average stock, so the cost per unit $Y$ rests on this value.
--
--   **Formalization Note** The average is the long-run (Cesàro) time average, written as a limit as $T \to \infty$ of $\frac1T\int_0^T$. The stock is a genuine function of time, never defined as $X/2$.
-- source:
--   Harris, How many parts to make at once, Operations Research 38(6) (1990), p. 948, left column, second and third paragraphs ("the stock consists of additions in lots of X and a gradual exhaustion of the stock to nothing"; "The average stock, if the movement is regular, it will be evident, is one-half of X")

import Mathlib
import Definitions.Def_HarrisEOQ_Lot_Setting

open Filter Topology

namespace HarrisEOQ.Lot

theorem average_stock_half (M X : ℝ) (hM : 0 < M) (hX : 0 < X) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, stockLevel M X t) atTop (𝓝 (X / 2)) := by sorry

end HarrisEOQ.Lot
