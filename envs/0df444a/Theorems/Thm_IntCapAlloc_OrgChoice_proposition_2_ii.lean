-- Prove2me | Theorems.Thm_IntCapAlloc_OrgChoice_proposition_2_ii
-- name    : IntCapAlloc.OrgChoice.proposition_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T08:40:21.664856+00:00
-- url     : https://prove2.me/theorems/fdd19d5f-03c1-4fcc-880b-3a6de2a75f8a
-- title:
--   Proposition 2 (ii), p. 11 — c < (1−p)/(2p), X < 2 + c: disclose exactly the profitable projects, k = number of profitable projects, efficiency 2p(X−1−c)
-- statement:
--   Consider the multi-divisional firm with $0 < p < 1$, $X > 1$, $c > 0$, $0 < q < 1$, $\beta > qX$ and $X \ge 1 + c$, and suppose
--   $$
--   c < \frac{1-p}{2p}, \qquad X < 2 + c.
--   $$
--   Then the highest equilibrium efficiency is $2p(X - 1 - c)$, and in every pure-strategy PBE the manager discloses $\theta_i$ exactly when $\theta_i = 1$, and on the equilibrium path investors fund $k = 2$ projects after $(D,D)$, $k = 1$ after one disclosure and $k = 0$ after $(ND,ND)$; that is, $k$ equals the number of profitable projects.
--
--   This is "equilibrium D" of the paper: with cheap disclosure and moderate cash flows, the firm finances exactly its profitable projects. It supplies the multi-divisional value in the region where Proposition 3 finds the two structures equally efficient.
--
--   Differences from the source:
--   - generalization: the proposition describes the selected equilibrium → the efficiency $2p(X-1-c)$ of the proof (p. 31) is added, and the description is stated for every equilibrium; reason: the proof states the value and "equilibrium D is unique" (p. 31); the clauses specialize to the printed claim.
--   - reading: "Investors choose $k = 2$ if $d_1 = d_2 = D$, …" → $k$ after the messages sent in equilibrium; reason: off-path $k$ depends on off-path beliefs, which the paper leaves free.
--   - reading: PBE item 5 → per coordinate, strict; reason: the rule is stated per project $i$.
--   - reading: item 4 → λ = 1 iff $\theta_1 \ge \theta_2$; reason: p. 11.
--   - reading: equilibria → pure disclosure strategies; reason: Appendix B.1.
--   - generalization: footnote 7, sufficiently high β → only $\beta > qX$; reason: the game uses β only through $\beta > qX$.
-- source:
--   Hwang, Internal Capital Allocation, Voluntary Disclosure, and Investment Efficiency, author manuscript (March 2025) of Management Science doi:10.1287/mnsc.2022.01295, p. 11, Proposition 2 (ii); efficiency and uniqueness from the proof of Proposition 2, Appendix A, pp. 30–31

import Mathlib
import Definitions.Def_IntCapAlloc_OrgChoice_Model

namespace IntCapAlloc.OrgChoice

/-- Proposition 2 (ii) (p. 11), with the efficiency value of its proof (p. 31). If
c < (1−p)/(2p) and X < 2 + c, every equilibrium of the multi-divisional firm has the manager
disclose exactly the profitable projects, and on the equilibrium path investors fund as many
projects as are profitable (k = 2 after (D, D), k = 1 after one disclosure, k = 0 after
(ND, ND)); the highest efficiency is 2p(X − 1 − c). -/
theorem proposition_2_ii (p X c q bet : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 < X) (hc : 0 < c)
    (hq0 : 0 < q) (hq1 : q < 1) (hbet : q * X < bet) (hfocus : 1 + c ≤ X)
    (hc1 : c < (1 - p) / (2 * p)) (hX2 : X < 2 + c) :
    IsGreatest (effSetM p X c q bet) (2 * p * (X - 1 - c)) ∧
    ∀ σ μ, IsEquilibrium p X c q bet σ μ →
      (∀ t, σ t = t) ∧
      ∀ t, invest X c μ (msg t (σ t)) = (if t 0 then 1 else 0) + (if t 1 then 1 else 0) := by sorry

end IntCapAlloc.OrgChoice
