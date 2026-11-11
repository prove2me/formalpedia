-- Prove2me | Theorems.Thm_NodeStableProj_Main_app_C_size_estimate_order
-- name    : NodeStableProj.Main.app_C_size_estimate_order
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:57:54.115195+00:00
-- url     : https://prove2.me/theorems/721c687a-6214-43de-b465-73563d919a12
-- title:
--   App. C — the size estimate overshoots by 2B = O(log(1/δ)/ε)
-- statement:
--   With the budget split $(\varepsilon_s,\delta_s)=(\varepsilon/2,\delta/2)$ and $B=\lceil(1/\varepsilon_s)\log(4/\delta_s)\rceil$, the deterministic upper bound $\hat n\le|V|+2B$ is $|V|+O(\log(1/\delta)/\varepsilon)$: there is a constant $C$ such that for all $\varepsilon,\delta\in(0,1)$
--   $$2B\ \le\ C\,\frac{\log(1/\delta)}{\varepsilon}.$$
--
--   This is how the paper converts the padding into the bound of Theorem 3.5 item 3.
--
--   Differences from the source:
--   - reading: "|V| + 2B = |V| + O(log(1/δ)/ε)" with (ε_s, δ_s) = (ε/2, δ/2) → ∃ C, ∀ ε, δ ∈ (0, 1): 2B ≤ C log(1/δ)/ε; reason: O(·) with a universal constant over the parameter range of Theorem 3.5; as printed (see finding I2)
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 33, Appendix C, "|V| + 2B = |V| + O(log(1/δ)/ε)"

import Mathlib
import Definitions.Def_PFRelease_Indist
import Definitions.Def_NodeStableProj_Main_SizeEstimate

open MeasureTheory

namespace NodeStableProj.Main

/-- Appendix C, p. 33, the order of the size estimate's slack: with `(ε_s, δ_s) = (ε/2, δ/2)`,
`|V| + 2B = |V| + O(log(1/δ)/ε)` — there is `C` with `2B ≤ C log(1/δ)/ε` for all
`ε, δ ∈ (0, 1)`. -/
theorem app_C_size_estimate_order :
    ∃ C : ℝ, ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      (2 * sizeB (ε / 2) (δ / 2) : ℝ) ≤ C * (Real.log (1 / δ) / ε) := by sorry

end NodeStableProj.Main
