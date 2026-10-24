-- Prove2me | Theorems.Thm_IntCapAlloc_OrgChoice_proposition_3
-- name    : IntCapAlloc.OrgChoice.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T08:40:26.474263+00:00
-- url     : https://prove2.me/theorems/d760275f-ddae-4b4d-adc9-c3abfbdd36ad
-- title:
--   Proposition 3, p. 13 — the founder's choice: multi-divisional strictly better on part (i)'s region, stand-alone on part (ii)'s, tie otherwise (corrected: tie on c = (1−p)/(2p))
-- statement:
--   Let $0 < p < 1$, $X > 1$, $c > 0$, $0 < q < 1$, $\beta > qX$, and $X \ge 1 + c$. Let $V_m$ be the highest investment efficiency over all pure-strategy perfect Bayesian equilibria of the multi-divisional firm, and $V_s$ the highest investment efficiency of the stand-alone structure (two firms, each in an equilibrium of its own game). Both maxima exist, and:
--
--   1. if $\frac{1-p}{2p} \le c < \frac{1-p^2}{2p^2}$ and $X < \min\{2 + c, \frac{1+p}{p}\}$, then $V_s \le V_m$; if moreover $c > \frac{1-p}{2p}$, then
--   $$
--   V_s < V_m \qquad \text{(the founder chooses } o^* = m\text{)};
--   $$
--   2. if $c < \frac{1-p}{p}$ and $X \ge 2 + c$, then
--   $$
--   V_m < V_s \qquad \text{(the founder chooses } o^* = s\text{)};
--   $$
--   3. otherwise — including the line $c = \frac{1-p}{2p}$ of part 1's region — $V_m = V_s$ (the founder is indifferent).
--
--   This is the paper's main result: an internal capital market beats two stand-alone firms exactly when disclosure costs are intermediate and cash flows are low, so that a multi-divisional manager raises capital without disclosing and allocates it internally to a profitable project; with low disclosure costs and high cash flows, the multi-divisional manager's empire building leads to over-investment and stand-alone firms are better.
--
--   Differences from the source:
--   - correction: (i) "the founder chooses $o^* = m$" on $\frac{1-p}{2p} \le c$ → strict preference only for $c > \frac{1-p}{2p}$, and $V_m = V_s$ on the line $c = \frac{1-p}{2p}$; reason: there both values equal $2pX - p - 1$, e.g. $p = 2/5$, $c = 3/4$, $X = 19/10$, $q = 1/2$, $\beta = 39/20$: $V_m = V_s = 3/25$.
--   - reading: Proposition 3 does not restate the parameter space → $X \ge 1 + c$ is a hypothesis; reason: the paper's standing focus (p. 9: "in subsequent analyses, I focus on … $X \ge 1 + c$", repeated p. 11), under which Propositions 1–2 and the proof (p. 33) hold.
--   - reading: "the founder chooses $o^* = m$ / $s$ / either" → $V_s < V_m$ / $V_m < V_s$ / $V_m = V_s$, with $V$ the greatest equilibrium efficiency of each structure; reason: PBE item 1 and "I focus on the equilibrium with the highest investment efficiency" (p. 8).
--   - reading: the stand-alone structure's selected equilibrium → the greatest sum of the two firms' equilibrium efficiencies; reason: the two firms' games are separate ((2), (5)).
--   - reading: PBE item 5 → per coordinate, strict; reason: the rule is stated per project $i$.
--   - reading: item 4 → λ = 1 iff $\theta_1 \ge \theta_2$; reason: p. 11.
--   - reading: equilibria → pure disclosure strategies; reason: Appendix B.1.
--   - generalization: footnote 7, sufficiently high β → only $\beta > qX$; reason: the game uses β only through $\beta > qX$.
-- source:
--   Hwang, Internal Capital Allocation, Voluntary Disclosure, and Investment Efficiency, author manuscript (March 2025) of Management Science doi:10.1287/mnsc.2022.01295, p. 13, Proposition 3

import Mathlib
import Definitions.Def_IntCapAlloc_OrgChoice_Model

namespace IntCapAlloc.OrgChoice

/-- Proposition 3 (p. 13), the founder's choice, corrected on the line c = (1−p)/(2p).
Under the standing focus X ≥ 1 + c, the highest equilibrium efficiencies `vm` of the
multi-divisional firm and `vs` of two stand-alone firms exist, and: on part (i)'s region
vs ≤ vm, strictly if moreover c > (1−p)/(2p) (the founder chooses o = m); on part (ii)'s region
vm < vs (the founder chooses o = s); elsewhere, including the line c = (1−p)/(2p) of part (i)'s
region, vm = vs (either structure). -/
theorem proposition_3 (p X c q bet : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 < X) (hc : 0 < c)
    (hq0 : 0 < q) (hq1 : q < 1) (hbet : q * X < bet) (hfocus : 1 + c ≤ X) :
    ∃ vm vs : ℝ, IsGreatest (effSetM p X c q bet) vm ∧ IsGreatest (effSetS p X c q bet) vs ∧
      ((1 - p) / (2 * p) ≤ c → c < (1 - p ^ 2) / (2 * p ^ 2) → X < min (2 + c) ((1 + p) / p) →
        vs ≤ vm) ∧
      ((1 - p) / (2 * p) < c → c < (1 - p ^ 2) / (2 * p ^ 2) → X < min (2 + c) ((1 + p) / p) →
        vs < vm) ∧
      (c < (1 - p) / p → 2 + c ≤ X → vm < vs) ∧
      (¬ ((1 - p) / (2 * p) < c ∧ c < (1 - p ^ 2) / (2 * p ^ 2) ∧ X < min (2 + c) ((1 + p) / p)) →
        ¬ (c < (1 - p) / p ∧ 2 + c ≤ X) → vm = vs) := by sorry

end IntCapAlloc.OrgChoice
