-- Prove2me | Theorems.Thm_IntCapAlloc_OrgChoice_proposition_2_i
-- name    : IntCapAlloc.OrgChoice.proposition_2_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T08:40:35.031085+00:00
-- url     : https://prove2.me/theorems/e938059d-7f62-4b78-aa20-74a3102db54d
-- title:
--   Proposition 2 (i), p. 11 — internal capital allocation region: (D, D) only at (1, 1), k = 2 / 1, efficiency p(2X−p(1+2c))−1 (corrected: unique only for c > (1−p)/(2p))
-- statement:
--   Consider the multi-divisional firm with $0 < p < 1$, $X > 1$, $c > 0$, $0 < q < 1$, $\beta > qX$ and $X \ge 1 + c$, and suppose
--   $$
--   \frac{1-p}{2p} \le c < \frac{1-p^2}{2p^2}, \qquad X < \min\Big\{2 + c,\ \frac{1+p}{p}\Big\}.
--   $$
--   Then:
--
--   1. the highest equilibrium efficiency is $p\big(2X - p(1 + 2c)\big) - 1$;
--   2. it is attained by an equilibrium ("equilibrium I") in which the manager chooses $(D, D)$ when $\theta_1 = \theta_2 = 1$ and $(ND, ND)$ otherwise, and investors choose $k = 2$ after $(D, D)$ and $k = 1$ after $(ND, ND)$;
--   3. if moreover $c > \frac{1-p}{2p}$, every equilibrium attaining the highest efficiency is of this form.
--
--   In equilibrium I the firm raises one unit without disclosure and the manager allocates it internally to a profitable project when there is one. Proposition 3 uses this value to show that the multi-divisional firm is strictly more efficient in this region.
--
--   Differences from the source:
--   - correction: the selected equilibrium is I ("the manager chooses …"), "selected as a unique equilibrium" (proof, pp. 29–30) → I attains the maximum, and is the only maximizer for $c > (1-p)/(2p)$; reason: at $c = (1-p)/(2p)$ equilibrium D (full disclosure of profitable projects) ties, e.g. $p = 2/5$, $c = 3/4$, $X = 19/10$, $q = 1/2$, $\beta = 39/20$: both have efficiency $3/25$.
--   - generalization: the proposition describes the selected equilibrium → the efficiency $p(2X - p(1+2c)) - 1$ of the proof (p. 29) is added; reason: the proof states the value; the clause specializes to the printed claim.
--   - reading: "Investors choose $k = 2$ if $d_1 = d_2 = D$ and $k = 1$ if $d_1 = d_2 = ND$" → $k$ after the messages sent in equilibrium; reason: off-path $k$ depends on off-path beliefs, which the paper leaves free.
--   - reading: PBE item 5 → per coordinate, strict; reason: the rule is stated per project $i$.
--   - reading: item 4 → λ = 1 iff $\theta_1 \ge \theta_2$; reason: p. 11.
--   - reading: equilibria → pure disclosure strategies; reason: Appendix B.1.
--   - generalization: footnote 7, sufficiently high β → only $\beta > qX$; reason: the game uses β only through $\beta > qX$.
-- source:
--   Hwang, Internal Capital Allocation, Voluntary Disclosure, and Investment Efficiency, author manuscript (March 2025) of Management Science doi:10.1287/mnsc.2022.01295, p. 11, Proposition 2 (i); efficiency from the proof of Proposition 2, Appendix A, pp. 29–30

import Mathlib
import Definitions.Def_IntCapAlloc_OrgChoice_Model

namespace IntCapAlloc.OrgChoice

/-- Proposition 2 (i) (p. 11), with the efficiency value of its proof (p. 29). If
(1−p)/(2p) ≤ c < (1−p²)/(2p²) and X < min{2 + c, (1+p)/p}, the highest efficiency of the
multi-divisional firm is p(2X − p(1 + 2c)) − 1, attained by an equilibrium in which the manager
chooses (D, D) at θ₁ = θ₂ = 1 and (ND, ND) otherwise, with k = 2 after (D, D) and k = 1 after
(ND, ND); for c > (1−p)/(2p) every equilibrium attaining it is of this form (corrected: at
c = (1−p)/(2p) the full-disclosure equilibrium D ties). -/
theorem proposition_2_i (p X c q bet : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 < X) (hc : 0 < c)
    (hq0 : 0 < q) (hq1 : q < 1) (hbet : q * X < bet) (hfocus : 1 + c ≤ X)
    (hc1 : (1 - p) / (2 * p) ≤ c) (hc2 : c < (1 - p ^ 2) / (2 * p ^ 2))
    (hX2 : X < min (2 + c) ((1 + p) / p)) :
    IsGreatest (effSetM p X c q bet) (p * (2 * X - p * (1 + 2 * c)) - 1) ∧
    (∃ μ, IsEquilibrium p X c q bet (fun t _ => t 0 && t 1) μ ∧
      (∀ t, invest X c μ (msg t (fun _ => t 0 && t 1)) = if (t 0 && t 1) then 2 else 1) ∧
      efficiency p X c (fun t _ => t 0 && t 1) μ = p * (2 * X - p * (1 + 2 * c)) - 1) ∧
    ((1 - p) / (2 * p) < c → ∀ σ μ, IsEquilibrium p X c q bet σ μ →
      efficiency p X c σ μ = p * (2 * X - p * (1 + 2 * c)) - 1 →
        σ = (fun t _ => t 0 && t 1) ∧
        ∀ t, invest X c μ (msg t (σ t)) = if (t 0 && t 1) then 2 else 1) := by sorry

end IntCapAlloc.OrgChoice
