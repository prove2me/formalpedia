-- Prove2me | Theorems.Thm_IntCapAlloc_OrgChoice_proposition_2_iii
-- name    : IntCapAlloc.OrgChoice.proposition_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T08:40:25.22199+00:00
-- url     : https://prove2.me/theorems/433fbd1d-ba7d-40fd-acde-cd8e324c1532
-- title:
--   Proposition 2 (iii), p. 11 — c < (1−p)/p, X ≥ 2 + c: disclose exactly the profitable projects, k = 2 unless (ND, ND), efficiency 2p(X+p−2−c)
-- statement:
--   Consider the multi-divisional firm with $0 < p < 1$, $X > 1$, $c > 0$, $0 < q < 1$, $\beta > qX$ and $X \ge 1 + c$, and suppose
--   $$
--   c < \frac{1-p}{p}, \qquad X \ge 2 + c.
--   $$
--   Then the highest equilibrium efficiency is $2p(X + p - 2 - c)$, and in every pure-strategy PBE the manager discloses $\theta_i$ exactly when $\theta_i = 1$, and on the equilibrium path investors choose $k = 0$ after $(ND, ND)$ and $k = 2$ otherwise.
--
--   This is "equilibrium $\hat D$": a single profitable project's cash flow covers the capital of both, so disclosing it secures funding for both projects, including the unprofitable one. Proposition 3 uses this value to show that two stand-alone firms are strictly more efficient in this region.
--
--   Differences from the source:
--   - generalization: the proposition describes the selected equilibrium → the efficiency $2p(X+p-2-c)$ of the proof (p. 31) is added, and the description is stated for every equilibrium; reason: the proof states the value and "equilibrium $\hat D$ is unique" (p. 32); the clauses specialize to the printed claim.
--   - reading: "Investors choose $k = 0$ if $d_1 = d_2 = ND$ and $k = 2$ otherwise" → $k$ after the messages sent in equilibrium; reason: off-path $k$ depends on off-path beliefs, which the paper leaves free.
--   - reading: PBE item 5 → per coordinate, strict; reason: the rule is stated per project $i$.
--   - reading: item 4 → λ = 1 iff $\theta_1 \ge \theta_2$; reason: p. 11.
--   - reading: equilibria → pure disclosure strategies; reason: Appendix B.1.
--   - generalization: footnote 7, sufficiently high β → only $\beta > qX$; reason: the game uses β only through $\beta > qX$.
-- source:
--   Hwang, Internal Capital Allocation, Voluntary Disclosure, and Investment Efficiency, author manuscript (March 2025) of Management Science doi:10.1287/mnsc.2022.01295, p. 11, Proposition 2 (iii); efficiency and uniqueness from the proof of Proposition 2, Appendix A, pp. 31–32

import Mathlib
import Definitions.Def_IntCapAlloc_OrgChoice_Model

namespace IntCapAlloc.OrgChoice

/-- Proposition 2 (iii) (p. 11), with the efficiency value of its proof (p. 31). If
c < (1−p)/p and X ≥ 2 + c, every equilibrium of the multi-divisional firm has the manager
disclose exactly the profitable projects, and on the equilibrium path investors choose k = 0
after (ND, ND) and k = 2 otherwise; the highest efficiency is 2p(X + p − 2 − c). -/
theorem proposition_2_iii (p X c q bet : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 < X) (hc : 0 < c)
    (hq0 : 0 < q) (hq1 : q < 1) (hbet : q * X < bet) (hfocus : 1 + c ≤ X)
    (hc1 : c < (1 - p) / p) (hX2 : 2 + c ≤ X) :
    IsGreatest (effSetM p X c q bet) (2 * p * (X + p - 2 - c)) ∧
    ∀ σ μ, IsEquilibrium p X c q bet σ μ →
      (∀ t, σ t = t) ∧
      ∀ t, invest X c μ (msg t (σ t)) = if (t 0 || t 1) then 2 else 0 := by sorry

end IntCapAlloc.OrgChoice
