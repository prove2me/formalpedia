-- Prove2me | Theorems.Thm_IPLicense3D_Pooling_proposition_2
-- name    : IPLicense3D.Pooling.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:29.408623+00:00
-- url     : https://prove2.me/theorems/71706ea5-5e29-47b5-9457-92442514621c
-- title:
--   Proposition 2, p. 2693 — for identical buyers a fixed fee S̄ or no licensing is optimal, and the optimal profit increases in w
-- statement:
--   Consider $n \ge 1$ identical buyers, all with demand rate $\lambda$, under the standing assumptions of §3. Write $S(f,r)$ for the common surplus and $\bar S = S(0,0)$ for the common maximum surplus.
--
--   1. If $\bar S \ge (w-c)\lambda$ and $\bar S \ge 0$, then the fixed-fee-only license $(f^*, r^*) = (\bar S, 0)$ is optimal. Every buyer takes it (a decentralized configuration), the OEM extracts all of the buyers' maximum surplus,
--   $$
--   \Pi(\bar S, 0) = n\bar S = \max_{f, r \ge 0} \Pi(f,r),
--   $$
--   and, if $\bar S > 0$, the efficacy is $\eta(\bar S, 0) = 1$.
--   2. If $\bar S < (w-c)\lambda$, then the optimal profit is $\max_{f, r \ge 0}\Pi(f,r) = (w-c)n\lambda$. A valid license attains it exactly when $S(f,r) < 0$, and then no buyer takes the license (a centralized configuration).
--   3. The optimal profit increases in $w$: if $w \le w'$, the least upper bound of the attainable profits at $w$ is at most that at $w'$.
--
--   This is the full characterization of the optimal license for identical buyers. Proposition 3 relies on it for the regions where only one buyer licenses.
--
--   **Formalization Note** Three hypotheses are added and disclosed. $n \ge 1$ is needed for the "exactly when" of part 2. $\bar S \ge 0$ makes $(\bar S, 0)$ a valid license; it is automatic when $w \ge c$. $\bar S > 0$ is needed for the efficacy, which the paper defines only when some buyer has positive maximum surplus. The optimum is stated as a greatest element of $\{\Pi(f,r) \mid f, r \ge 0\}$. The paper's license "$(\infty,\infty)$" is read as "any license with $S(f,r) < 0$". "Increases" is stated in the weak sense, between least upper bounds.
-- source:
--   Zhang, Westerweel, Basten & Song, Distributed 3D Printing of Spare Parts via IP Licensing, MSOM 24(5) 2022, p. 2693, Proposition 2; proof pp. 2699–2700

import Mathlib
import Definitions.Def_IPLicense3D_Pooling_Model

namespace IPLicense3D.Pooling
open Model

theorem proposition_2 {n : ℕ} (M : Model n) (hM : M.Standing) (hn : 0 < n) (lam : ℝ)
    (hlam : ∀ i, M.lam i = lam) :
    ((M.w - M.c) * lam ≤ M.surplusL lam 0 0 → 0 ≤ M.surplusL lam 0 0 →
      M.oemProfit (M.surplusL lam 0 0) 0 = n * M.surplusL lam 0 0 ∧
      IsGreatest M.validProfits (n * M.surplusL lam 0 0) ∧
      M.optsIn (M.surplusL lam 0 0) 0 = Finset.univ ∧
      (0 < M.surplusL lam 0 0 → M.efficacy (M.surplusL lam 0 0) 0 = 1)) ∧
    (M.surplusL lam 0 0 < (M.w - M.c) * lam →
      IsGreatest M.validProfits ((M.w - M.c) * n * lam) ∧
      (∀ f r : ℝ, 0 ≤ f → 0 ≤ r →
        (M.oemProfit f r = (M.w - M.c) * n * lam ↔ M.surplusL lam f r < 0)) ∧
      (∀ f r : ℝ, M.surplusL lam f r < 0 → M.optsIn f r = ∅)) ∧
    (∀ w' : ℝ, M.w ≤ w' → ∀ v v' : ℝ,
      IsLUB M.validProfits v → IsLUB (M.withW w').validProfits v' → v ≤ v') := by sorry

end IPLicense3D.Pooling
