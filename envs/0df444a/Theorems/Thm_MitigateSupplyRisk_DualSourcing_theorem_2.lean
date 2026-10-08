-- Prove2me | Theorems.Thm_MitigateSupplyRisk_DualSourcing_theorem_2
-- name    : MitigateSupplyRisk.DualSourcing.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:37.739696+00:00
-- url     : https://prove2.me/theorems/13c34594-5e47-4b67-b1b7-6224133c32c9
-- title:
--   Theorem 2, pp. 494–495 — optimal dual-sourcing quantities region by region (corrected Ω₃–Ω₅ bounds)
-- statement:
--   Consider the two-supplier random-capacity newsvendor at reliability indices $a = (a_1, a_2)$ and suppose that
--
--   1. demand is deterministic, equal to $x \ge 0$;
--   2. there is no committed cost, $\eta_1 = \eta_2 = 0$, so $\phi_i = (r + p - c_i)/(r + p - v)$;
--   3. $0 < \phi_i < 1$ for $i = 1, 2$, that is, $v < c_i < r + p$;
--   4. each capacity-loss distribution $G_i(\cdot) = G_i(\cdot, a_i)$ is strictly increasing on its support $[0, b_i]$, with $b_i \le K_i$, so that $G_i(K_i) = 1$;
--   5. $\phi_1 G_1(K_1) \ge \phi_2 G_2(K_2)$ (a labelling of the suppliers).
--
--   Write $A_1 = G_1^{-1}(\phi_2)$, $A_2 = G_2^{-1}(\phi_1)$, $B = G_1^{-1}\big(\tfrac{\phi_2}{\phi_1} G_2(K_2)\big)$ and $S = K_1 + K_2$. Then an optimal procurement vector $q^* = (q_1^*, q_2^*)$, maximizing $\Pi_2(\cdot\,; a)$ over all $q \ge 0$, is given by
--   $$\begin{aligned}
--   &\Omega_1:\ 0 \le x \le K_1 - B && q^* = (x,\ 0),\\
--   &\Omega_2:\ K_1 - B < x \le S - (A_1 + A_2) && q^* = (x - q_2^*,\ q_2^*),\ \ \phi_1 G_1(K_1 - (x - q_2^*)) = \phi_2 G_2(K_2 - q_2^*),\\
--   &\Omega_3:\ S - (A_1 + A_2) < x \le S - \max(A_1, A_2) && q^* = (x - (K_2 - A_2),\ x - (K_1 - A_1)),\\
--   &\Omega_4:\ S - \max(A_1, A_2) < x \le S - \min(A_1, A_2) && q^* = \begin{cases}(x - (K_2 - A_2),\ K_2) & \text{if } A_1 \ge A_2,\\ (K_1,\ x - (K_1 - A_1)) & \text{if } A_1 < A_2,\end{cases}\\
--   &\Omega_5 \cup \Omega_6:\ x > S - \min(A_1, A_2) && q^* = (K_1,\ K_2).
--   \end{aligned}$$
--   In $\Omega_2$ the claim is that some $q_2^* \in [0, x]$ solves the displayed equation and makes $(x - q_2^*, q_2^*)$ optimal.
--
--   The regions trace the firm's strategy as demand grows: single sourcing from the preferred supplier when capacity is ample ($\Omega_1$), dual sourcing with total order equal to demand ($\Omega_2$), dual sourcing with over-ordering, the **quantity hedge** ($\Omega_3$, $\Omega_4$, $\Omega_5$), and finally ordering both full capacities ($\Omega_6$, $x > S$).
--
--   **Formalization Note.** Three corrections to the printed theorem. (i) The printed bounds of $\Omega_3, \Omega_4, \Omega_5$ use $\min$ where $\max$ belongs and vice versa; as printed, $\Omega_4$ is empty and $\Omega_3$ overlaps $\Omega_5$, and the printed $\Omega_3$ formula can order more than $K_1$ from supplier 1 (e.g. uniform losses on $[0,60]$, $[0,80]$, $K = (100,100)$, $\phi = (0.9, 0.85)$, $x = 140$ gives $q_1^* = 112$). The bounds above are the corrected ones. (ii) Hypothesis 4 is added: without $G_i(K_i) = 1$ the $\Omega_1$ claim is false (exponential losses with $G(K) \approx 0.865$ give a counterexample), and strict increase makes $G_i^{-1}$ and the $\Omega_2$ equation well posed; continuity of $G_i$ is the paper's own assumption. (iii) Hypothesis 3 is added; it makes $G_i^{-1}(\phi_j)$ and $G_1^{-1}(\phi_2/\phi_1)$ evaluate inside $(0, 1)$. $G_i^{-1}$ is the generalized inverse $\inf\{t \ge 0 : G_i(t) \ge u\}$, the ordinary inverse under hypothesis 4. Deterministic demand is the point mass $\delta_x$. Optimal vectors need not be unique (in $\Omega_6$ any $q \ge (K_1, K_2)$ is optimal), so the theorem asserts that the displayed vector is *an* optimal one. In the Lean statement supplier 1 is index `0` and supplier 2 is index `1`.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), pp. 494–495 (PDF pp. 6–7), Theorem 2 (with the preamble on p. 494)

import Mathlib
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Model
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Regions

open MeasureTheory ProbabilityTheory

namespace MitigateSupplyRisk.DualSourcing

/-- Theorem 2 (Wang, Gilland, Tomlin 2010, pp. 494–495), with the region bounds of `Ω₃, Ω₄, Ω₅`
corrected (the printed `min`/`max` are swapped) and the hypotheses the printed statement needs.
Demand is deterministic (`μ = δ_x`, `x ≥ 0`), `η = 0`, `0 < φ_i < 1`, each capacity-loss CDF
`G_i(·, a_i)` is strictly increasing on its support `[0, b_i]` with `b_i ≤ K_i` (so
`G_i(K_i, a_i) = 1`), and `φ₁ G₁(K₁) ≥ φ₂ G₂(K₂)`. With `A₁ = G₁^{-1}(φ₂)`, `A₂ = G₂^{-1}(φ₁)`,
`B = G₁^{-1}((φ₂/φ₁) G₂(K₂))` and `S = K₁ + K₂`, an optimal procurement vector is
* `Ω₁` (`x ≤ K₁ − B`): `(x, 0)`;
* `Ω₂` (`K₁ − B < x ≤ S − (A₁ + A₂)`): `(x − q₂, q₂)` for some `q₂ ∈ [0, x]` solving
  `φ₁ G₁(K₁ − (x − q₂)) = φ₂ G₂(K₂ − q₂)`;
* `Ω₃` (`S − (A₁ + A₂) < x ≤ S − max(A₁, A₂)`): `(x − (K₂ − A₂), x − (K₁ − A₁))`;
* `Ω₄` (`S − max(A₁, A₂) < x ≤ S − min(A₁, A₂)`): `(x − (K₂ − A₂), K₂)` if `A₁ ≥ A₂`, and
  `(K₁, x − (K₁ − A₁))` if `A₁ < A₂`;
* `Ω₅ ∪ Ω₆` (`x > S − min(A₁, A₂)`): `(K₁, K₂)`.
Supplier 1 of the paper is index `0`, supplier 2 is index `1`. -/
theorem theorem_2 (M : Model) (a : Fin 2 → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hη : ∀ i, M.η i = 0)
    (hφpos : ∀ i, 0 < M.phi i) (hφlt : ∀ i, M.phi i < 1)
    (hsupp : ∀ i, ∃ b : ℝ, 0 < b ∧ b ≤ M.K i ∧ M.G i b (a i) = 1 ∧
      StrictMonoOn (fun t => M.G i t (a i)) (Set.Icc 0 b))
    (hord : M.phi 1 * M.G 1 (M.K 1) (a 1) ≤ M.phi 0 * M.G 0 (M.K 0) (a 0)) :
    -- Ω₁
    (x ≤ M.K 0 - M.B a →
      M.IsOptimal (Measure.dirac x) a ![x, 0]) ∧
    -- Ω₂
    (M.K 0 - M.B a < x ∧ x ≤ M.K 0 + M.K 1 - (M.A1 a + M.A2 a) →
      ∃ q₂ : ℝ, 0 ≤ q₂ ∧ q₂ ≤ x ∧
        M.phi 0 * M.G 0 (M.K 0 - (x - q₂)) (a 0) = M.phi 1 * M.G 1 (M.K 1 - q₂) (a 1) ∧
        M.IsOptimal (Measure.dirac x) a ![x - q₂, q₂]) ∧
    -- Ω₃ (corrected upper bound)
    (M.K 0 + M.K 1 - (M.A1 a + M.A2 a) < x ∧ x ≤ M.K 0 + M.K 1 - max (M.A1 a) (M.A2 a) →
      M.IsOptimal (Measure.dirac x) a ![x - (M.K 1 - M.A2 a), x - (M.K 0 - M.A1 a)]) ∧
    -- Ω₄ (corrected bounds)
    (M.K 0 + M.K 1 - max (M.A1 a) (M.A2 a) < x ∧ x ≤ M.K 0 + M.K 1 - min (M.A1 a) (M.A2 a) →
      (M.A2 a ≤ M.A1 a → M.IsOptimal (Measure.dirac x) a ![x - (M.K 1 - M.A2 a), M.K 1]) ∧
      (M.A1 a < M.A2 a → M.IsOptimal (Measure.dirac x) a ![M.K 0, x - (M.K 0 - M.A1 a)])) ∧
    -- Ω₅ ∪ Ω₆ (corrected lower bound of Ω₅)
    ((M.K 0 + M.K 1 - min (M.A1 a) (M.A2 a) < x ∧ x ≤ M.K 0 + M.K 1) ∨ M.K 0 + M.K 1 < x →
      M.IsOptimal (Measure.dirac x) a ![M.K 0, M.K 1]) := by sorry

end MitigateSupplyRisk.DualSourcing
