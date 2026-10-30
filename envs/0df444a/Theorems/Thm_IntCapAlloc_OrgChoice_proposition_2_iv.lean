-- Prove2me | Theorems.Thm_IntCapAlloc_OrgChoice_proposition_2_iv
-- name    : IntCapAlloc.OrgChoice.proposition_2_iv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T08:40:26.089598+00:00
-- url     : https://prove2.me/theorems/06941f93-d549-4827-9549-866d126103c6
-- title:
--   Proposition 2 (iv), p. 11 — high c and X: no disclosure, k = 2, efficiency 2(pX−1) (corrected: not unique on c = (1−p²)/(2p²), X < (1+p)/p)
-- statement:
--   Consider the multi-divisional firm with $0 < p < 1$, $X > 1$, $c > 0$, $0 < q < 1$, $\beta > qX$ and $X \ge 1 + c$, and suppose
--   $$
--   \Big(c \ge \frac{1-p}{p} \ \text{ and } \ X \ge \frac{1+p}{p}\Big) \quad \text{or} \quad c \ge \frac{1-p^2}{2p^2}.
--   $$
--   Then:
--
--   1. the highest equilibrium efficiency is $2(pX - 1)$;
--   2. it is attained by an equilibrium ("equilibrium ND") in which the manager never discloses and investors fund both projects ($k = 2$);
--   3. except on the line $c = \frac{1-p^2}{2p^2}$ with $X < \frac{1+p}{p}$, every equilibrium attaining the highest efficiency is of this form.
--
--   With costly disclosure and high cash flows, silence secures funding for both projects. Together with Proposition 1 (ii), this gives the region where Proposition 3 finds the two structures equally efficient.
--
--   Differences from the source:
--   - correction: equilibrium ND "is selected as a unique equilibrium" (proof, p. 33) → it attains the maximum, and is the only maximizer off the line $c = (1-p^2)/(2p^2)$, $X < (1+p)/p$; reason: on that line equilibrium I ties, e.g. $p = 3/5$, $c = 8/9$, $X = 11/5$, $q = 1/2$, $\beta = 21/10$: both have efficiency $16/25$.
--   - generalization: the proposition describes the selected equilibrium → the efficiency $2(pX - 1)$ of the proof (p. 32) is added; reason: the proof states the value; the clause specializes to the printed claim.
--   - reading: "If $c \ge \frac{1-p}{p}$ and $X \ge \frac{1+p}{p}$ or $c \ge \frac{1-p^2}{2p^2}$" → $(A \wedge B) \vee C$; reason: the other parse $A \wedge (B \vee C)$ gives the same set, since $\frac{1-p^2}{2p^2} > \frac{1-p}{p}$.
--   - reading: "investors choose $k = 2$" → $k$ after the message sent in equilibrium; reason: off-path $k$ depends on off-path beliefs, which the paper leaves free.
--   - reading: PBE item 5 → per coordinate, strict; reason: the rule is stated per project $i$.
--   - reading: item 4 → λ = 1 iff $\theta_1 \ge \theta_2$; reason: p. 11.
--   - reading: equilibria → pure disclosure strategies; reason: Appendix B.1.
--   - generalization: footnote 7, sufficiently high β → only $\beta > qX$; reason: the game uses β only through $\beta > qX$.
-- source:
--   Hwang, Internal Capital Allocation, Voluntary Disclosure, and Investment Efficiency, author manuscript (March 2025) of Management Science doi:10.1287/mnsc.2022.01295, p. 11, Proposition 2 (iv); efficiency from the proof of Proposition 2, Appendix A, pp. 32–33

import Mathlib
import Definitions.Def_IntCapAlloc_OrgChoice_Model

namespace IntCapAlloc.OrgChoice

/-- Proposition 2 (iv) (p. 11), with the efficiency value of its proof (p. 32). If
c ≥ (1−p)/p and X ≥ (1+p)/p, or c ≥ (1−p²)/(2p²), the highest efficiency of the
multi-divisional firm is 2(pX − 1), attained by an equilibrium in which the manager never
discloses and investors fund both projects; every equilibrium attaining it is of this form,
except on the line c = (1−p²)/(2p²) with X < (1+p)/p (corrected: there equilibrium I ties). -/
theorem proposition_2_iv (p X c q bet : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 < X) (hc : 0 < c)
    (hq0 : 0 < q) (hq1 : q < 1) (hbet : q * X < bet) (hfocus : 1 + c ≤ X)
    (hreg : ((1 - p) / p ≤ c ∧ (1 + p) / p ≤ X) ∨ (1 - p ^ 2) / (2 * p ^ 2) ≤ c) :
    IsGreatest (effSetM p X c q bet) (2 * (p * X - 1)) ∧
    (∃ μ, IsEquilibrium p X c q bet (fun _ _ => false) μ ∧
      (∀ t, invest X c μ (msg t (fun _ => false)) = 2) ∧
      efficiency p X c (fun _ _ => false) μ = 2 * (p * X - 1)) ∧
    (¬ (c = (1 - p ^ 2) / (2 * p ^ 2) ∧ X < (1 + p) / p) →
      ∀ σ μ, IsEquilibrium p X c q bet σ μ → efficiency p X c σ μ = 2 * (p * X - 1) →
        σ = (fun _ _ => false) ∧ ∀ t, invest X c μ (msg t (σ t)) = 2) := by sorry

end IntCapAlloc.OrgChoice
