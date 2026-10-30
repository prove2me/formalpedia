-- Prove2me | Theorems.Thm_IntCapAlloc_OrgChoice_proposition_1
-- name    : IntCapAlloc.OrgChoice.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T08:40:30.565934+00:00
-- url     : https://prove2.me/theorems/3bb3066a-d91a-4658-aaba-3c3ff160040c
-- title:
--   Proposition 1, p. 9 — stand-alone firm: disclose θᵢ = 1 iff c < (1−p)/p, efficiencies p(X−1−c) and pX−1 (corrected: uniqueness only for c > (1−p)/p)
-- statement:
--   Consider one stand-alone firm with parameters $0 < p < 1$, $X > 1$, $c > 0$, $0 < q < 1$, $\beta > qX$ and $X \ge 1 + c$.
--
--   1. If $c < \frac{1-p}{p}$, then in **every** pure-strategy PBE the manager discloses $\theta_i = 1$ and withholds $\theta_i = 0$; investors invest ($k_i = 1$) after the disclosure of $\theta_i = 1$ and do not invest ($k_i = 0$) after silence. The highest equilibrium efficiency is
--   $$
--   p(X - 1 - c).
--   $$
--   2. If $c \ge \frac{1-p}{p}$, the highest equilibrium efficiency is
--   $$
--   pX - 1,
--   $$
--   and it is attained by an equilibrium in which the manager never discloses and investors invest ($k_i = 1$). If moreover $c > \frac{1-p}{p}$, every equilibrium attaining $pX - 1$ is of this form.
--
--   This is the stand-alone benchmark: twice the highest efficiency of one firm is the value of the stand-alone structure that Proposition 3 compares with the multi-divisional firm.
--
--   Differences from the source:
--   - correction: (ii) the selected equilibrium is "ND, $k_i = 1$", "selected as a unique equilibrium" (proof, p. 29) → it attains the maximum, and is the only maximizer for $c > (1-p)/p$; reason: at $c = (1-p)/p$ the disclosing equilibrium ties, e.g. $p = 2/5$, $c = 3/2$, $X = 3$, $q = 1/2$, $\beta = 5/2$: both equilibria have efficiency $1/5$.
--   - generalization: the proposition describes the selected equilibrium → the efficiency values of the proof (p. 28) are added as clauses, and part (i) is stated for every equilibrium; reason: the proof states both values and "a unique equilibrium" (p. 29); the clauses specialize to the printed claims.
--   - reading: "investors choose $k_i$" → $k_i$ after the messages sent in equilibrium; reason: off-path $k_i$ depends on off-path beliefs, which the paper leaves free.
--   - reading: PBE item 5 → if the manager discloses, withholding gives a strictly lower payoff; reason: the tie rule as stated.
--   - reading: equilibria → pure disclosure strategies; reason: $d_i \in \{D, ND\}$ in the equilibrium definition.
--   - generalization: footnote 7, sufficiently high β → only $\beta > qX$; reason: the game uses β only through $\beta > qX$.
-- source:
--   Hwang, Internal Capital Allocation, Voluntary Disclosure, and Investment Efficiency, author manuscript (March 2025) of Management Science doi:10.1287/mnsc.2022.01295, p. 9, Proposition 1; efficiencies from the proof of Proposition 1, Appendix A, pp. 28–29

import Mathlib
import Definitions.Def_IntCapAlloc_OrgChoice_Model

namespace IntCapAlloc.OrgChoice

/-- Proposition 1 (p. 9), with the efficiency values of its proof (p. 28). A stand-alone firm,
X ≥ 1 + c. (i) If c < (1−p)/p, every equilibrium has the manager disclose θ = 1 (investors
then invest) and withhold θ = 0 (investors then do not invest), and the highest efficiency is
p(X − 1 − c). (ii) If c ≥ (1−p)/p, the highest efficiency is pX − 1, attained by an
equilibrium in which the manager never discloses and investors invest; for c > (1−p)/p every
equilibrium attaining it is of this form (corrected: at c = (1−p)/p the disclosing
equilibrium ties). -/
theorem proposition_1 (p X c q bet : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 < X) (hc : 0 < c)
    (hq0 : 0 < q) (hq1 : q < 1) (hbet : q * X < bet) (hfocus : 1 + c ≤ X) :
    (c < (1 - p) / p →
      IsGreatest (effSet1 p X c q bet) (p * (X - 1 - c)) ∧
      ∀ σ μ, IsEquilibrium1 p X c q bet σ μ →
        σ true = true ∧ σ false = false ∧
        invest1 X c μ (msg1 true true) = 1 ∧ invest1 X c μ (msg1 false false) = 0) ∧
    ((1 - p) / p ≤ c →
      IsGreatest (effSet1 p X c q bet) (p * X - 1) ∧
      (∃ μ, IsEquilibrium1 p X c q bet (fun _ => false) μ ∧ invest1 X c μ none = 1 ∧
        efficiency1 p X c (fun _ => false) μ = p * X - 1) ∧
      ((1 - p) / p < c → ∀ σ μ, IsEquilibrium1 p X c q bet σ μ →
        efficiency1 p X c σ μ = p * X - 1 →
          σ = (fun _ => false) ∧ invest1 X c μ none = 1)) := by sorry

end IntCapAlloc.OrgChoice
