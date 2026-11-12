-- Prove2me | Theorems.Thm_NodeStableProj_Main_app_C_size_estimate_order_delta_le_half
-- name    : NodeStableProj.Main.app_C_size_estimate_order_delta_le_half
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:14:16.895012+00:00
-- url     : https://prove2.me/theorems/1ff40f55-e7cb-486b-b2f2-a419878299d8
-- title:
--   App. C size-estimate slack 2B = O(log(1/δ)/ε) for δ ≤ 1/2 (corrected: false for δ near 1)
-- statement:
--   **Source** (App. C, p. 33): with $(\varepsilon_s, \delta_s) = (\varepsilon/2, \delta/2)$ and $B = \lceil (1/\varepsilon_s) \log(4/\delta_s) \rceil$, $|V| + 2B = |V| + O(\log(1/\delta)/\varepsilon)$, read as: there is $C$ with $2B \le C \log(1/\delta)/\varepsilon$ for all $\varepsilon, \delta \in (0, 1)$.
--
--   **Variant:** there is $C$ with $2B \le C \log(1/\delta)/\varepsilon$ for all $\varepsilon \in (0, 1)$ and $\delta \in (0, 1/2]$.
--
--   **Difference:** the variant restricts $\delta$ to $(0, 1/2]$, the range of Theorem 3.5 items 3–4, where the claim holds; the printed range includes $\delta$ near $1$, where it fails.
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 33, Appendix C (corrected)

import Mathlib
import Definitions.Def_NodeStableProj_Main_SizeEstimate

open MeasureTheory

theorem NodeStableProj.Main.app_C_size_estimate_order_delta_le_half :
    ∃ C : ℝ, ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ ≤ 1 / 2 →
      (2 * NodeStableProj.Main.sizeB (ε / 2) (δ / 2) : ℝ) ≤ C * (Real.log (1 / δ) / ε) := by sorry
