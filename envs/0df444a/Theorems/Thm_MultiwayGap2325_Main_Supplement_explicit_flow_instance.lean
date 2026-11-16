-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_explicit_flow_instance
-- name    : MultiwayGap2325.Main.Supplement.explicit_flow_instance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:23:08.024444+00:00
-- url     : https://prove2.me/theorems/87a244fc-5503-4248-a788-c921bb342325
-- title:
--   Theorem 3.5 — Explicit affine flow instance
-- statement:
--   There exists a genuine flow instance on the full real simplex $\Delta_{10}$ at threshold $T=3/5$, with affine label flows on every truncated face and constant weight densities, whose fractional cost $L$ is positive and whose value is
--
--   $$\frac{B-R}{L}=\frac{9999320418500}{8180229294583}.$$
--
--   Here $B$, $R$ and $L$ are the actual geometric integrals of the instance's terminal densities, allowances and interior weights. The rational has decimal expansion $1.2223765445\ldots$; it is not replaced by a truncated decimal. This supplies the paper's explicit affine certificate independently of any numerical search or optimality assertion.
--
--   **Formalization Note** Affine fields are restrictions of continuous affine maps on the coordinate vector space. Constant weights include the terminal densities. The raw data type carries no validity proof; all flow conditions occur in the existential conclusion.
--
--   Differences from the source:
--   - encoding: a flow instance with defined positive value (B-R)/L → raw geometric FlowData 10 together with validity, affine and constant-density predicates, L > 0 and the exact ratio; reason: the predicates state the source properties operationally and the explicit positivity excludes undefined division without excluding any source witness
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Theorem 3.5, p. 8

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

namespace MultiwayGap2325.Main.Supplement

/-- Theorem 3.5, p.8: a genuine geometric flow instance, with integrals computed from its densities. -/
theorem explicit_flow_instance :
    ∃ D : FlowData 10, IsFlowInstance (3 / 5) D ∧
      HasAffineLabelFlows (3 / 5) D ∧ HasConstantWeights (3 / 5) D ∧
      0 < totalL (3 / 5) D.weighting ∧
      (totalB (3 / 5) D.weighting - totalR (3 / 5) D) / totalL (3 / 5) D.weighting =
        (9999320418500 : ℝ) / 8180229294583 := by sorry

end MultiwayGap2325.Main.Supplement
