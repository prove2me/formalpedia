-- Prove2me | Theorems.Thm_IPLicense3D_Pooling_proposition_3
-- name    : IPLicense3D.Pooling.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:37.376276+00:00
-- url     : https://prove2.me/theorems/fb6f4a01-3c2b-4786-a5f0-19aa3ed0ff77
-- title:
--   Proposition 3 and Table 1, pp. 2694–2695 — the optimal standard IP license for two nonidentical buyers
-- statement:
--   Consider two buyers with demand rates $\lambda_1 < \lambda_2$ and positive maximum surpluses $\bar S_1, \bar S_2 > 0$, under the standing assumptions of §3. The OEM offers both buyers the same license $(f,r)$ with $f, r \ge 0$. Write $V$ for the optimal profit, the least upper bound of $\{\Pi(f,r) \mid f, r \ge 0\}$. Let $\bar r_1(0), \bar r_2(0) \ge 0$ be the maximum royalty fees ($S_i(0,\bar r_i(0)) = 0$), and $\hat r \ge 0$ a solution of $S_1(0,\hat r) = S_2(0,\hat r)$ (Lemma 2). In Lean, Buyer 1 is index `0` and Buyer 2 is index `1`.
--
--   In each case of Table 1 (p. 2695), $V$ is the largest entry of the case's profit column, and the listed licenses realize the listed profits and channel selections.
--
--   **Case I**, $\bar S_1 \le \bar S_2$ and $\bar r_2(0) \le \bar r_1(0)$:
--   $$
--   V = \max\{(w-c)\lambda_1 + \bar S_2,\ 2\bar S_1,\ 2S_1(0,\hat r) + \hat r(\lambda_1+\lambda_2),\ (w-c)\lambda_2 + S_1(0,\hat r) + \hat r\lambda_1,\ (w-c)(\lambda_1+\lambda_2)\}.
--   $$
--   The license $(S_1(0,\hat r), \hat r)$ is valid, both buyers take it, and it earns $2S_1(0,\hat r) + \hat r(\lambda_1+\lambda_2)$ (row iii). If $S_1(0,\hat r) > 0$, then for every small $\epsilon > 0$ the license $(S_1(0,\hat r+\epsilon), \hat r+\epsilon)$ is valid and taken by Buyer 1 alone, and its profit tends to $(w-c)\lambda_2 + S_1(0,\hat r) + \hat r\lambda_1$ as $\epsilon \downarrow 0$ (row iv, which is approached but not attained).
--
--   **Case II**, $\bar S_1 \le \bar S_2$ and $\bar r_2(0) > \bar r_1(0)$:
--   $$
--   V = \max\{(w-c)\lambda_1 + \bar S_2,\ 2\bar S_1,\ \bar r_1(0)(\lambda_1+\lambda_2),\ (w-c)(\lambda_1+\lambda_2)\},
--   $$
--   and the royalty-only license $(0, \bar r_1(0))$ is taken by both buyers and earns $\bar r_1(0)(\lambda_1+\lambda_2)$ (row iii).
--
--   **Case III**, $\bar S_1 > \bar S_2$:
--   $$
--   V = \max\{2\bar S_2,\ (w-c)\lambda_2 + \bar S_1,\ (w-c)(\lambda_1+\lambda_2)\}.
--   $$
--   $(\bar S_2, 0)$ is taken by both and earns $2\bar S_2$; $(\bar S_1, 0)$ is taken by Buyer 1 alone and earns $(w-c)\lambda_2 + \bar S_1$.
--
--   **Rows shared by Cases I and II.** If $\bar S_1 \le \bar S_2$, then $(\bar S_1, 0)$ is taken by both buyers and earns $2\bar S_1$ (row ii). If $\bar S_1 < \bar S_2$, then $(\bar S_2, 0)$ is taken by Buyer 2 alone and earns $(w-c)\lambda_1 + \bar S_2$ (row i).
--
--   **The license $(\infty,\infty)$.** Some valid license leaves both buyers with negative surplus. Every such license is taken by nobody and earns $(w-c)(\lambda_1+\lambda_2)$.
--
--   **Moreover**, the optimal profit increases in $w$: if $w \le w'$, then $V$ at $w$ is at most $V$ at $w'$.
--
--   This is the paper's main result. With a standard license and nonidentical buyers, the optimal license can be fixed-fee only, royalty only or mixed. The supply chain can be centralized, decentralized or hybrid.
--
--   **Formalization Note** The optimum is stated with `IsLUB`, because row iv is a supremum that no license attains. $\hat r$, $\bar r_1(0)$ and $\bar r_2(0)$ are bound by their defining equations; Corollary 1 and Lemma 2 make them exist and be unique. The paper's "$(\infty,\infty)$" means any license with $S_1, S_2 < 0$. Two boundary corrections (labelled): row i's channel selection "T, A" is stated for $\bar S_1 < \bar S_2$, because at equality Buyer 1 takes the license too. Row iv's approximating licenses are stated for $S_1(0,\hat r) > 0$, because otherwise they carry a negative fixed fee. The value formulas need neither correction. "Increases" is stated in the weak sense, between least upper bounds.
-- source:
--   Zhang, Westerweel, Basten & Song, Distributed 3D Printing of Spare Parts via IP Licensing, MSOM 24(5) 2022, p. 2694, Proposition 3; p. 2695, Table 1; proof pp. 2700–2701

import Mathlib
import Definitions.Def_IPLicense3D_Pooling_Model
open Filter Topology

namespace IPLicense3D.Pooling
open Model

theorem proposition_3 (M : Model 2) (hM : M.Standing) (hlam : M.lam 0 < M.lam 1)
    (hS0 : 0 < M.maxSurplus 0) (hS1 : 0 < M.maxSurplus 1) (rb0 rb1 : ℝ)
    (hrb0 : 0 ≤ rb0 ∧ M.surplus 0 0 rb0 = 0) (hrb1 : 0 ≤ rb1 ∧ M.surplus 1 0 rb1 = 0) :
    (M.maxSurplus 0 ≤ M.maxSurplus 1 → rb1 ≤ rb0 →
      ∀ rh : ℝ, 0 ≤ rh → M.surplus 0 0 rh = M.surplus 1 0 rh →
        IsLUB M.validProfits (M.caseIValue rh) ∧
        (0 ≤ M.surplus 0 0 rh ∧
          M.oemProfit (M.surplus 0 0 rh) rh = 2 * M.surplus 0 0 rh + rh * (M.lam 0 + M.lam 1) ∧
          M.optsIn (M.surplus 0 0 rh) rh = Finset.univ) ∧
        (0 < M.surplus 0 0 rh →
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ M.surplus 0 0 (rh + ε) ∧ 0 ≤ rh + ε ∧
            M.optsIn (M.surplus 0 0 (rh + ε)) (rh + ε) = {0}) ∧
          Tendsto (fun ε => M.oemProfit (M.surplus 0 0 (rh + ε)) (rh + ε)) (𝓝[>] 0)
            (𝓝 ((M.w - M.c) * M.lam 1 + M.surplus 0 0 rh + rh * M.lam 0)))) ∧
    (M.maxSurplus 0 ≤ M.maxSurplus 1 → rb0 < rb1 →
      IsLUB M.validProfits (M.caseIIValue rb0) ∧
      M.oemProfit 0 rb0 = rb0 * (M.lam 0 + M.lam 1) ∧ M.optsIn 0 rb0 = Finset.univ) ∧
    (M.maxSurplus 1 < M.maxSurplus 0 →
      IsLUB M.validProfits M.caseIIIValue ∧
      (M.oemProfit (M.maxSurplus 1) 0 = 2 * M.maxSurplus 1 ∧
        M.optsIn (M.maxSurplus 1) 0 = Finset.univ) ∧
      (M.oemProfit (M.maxSurplus 0) 0 = (M.w - M.c) * M.lam 1 + M.maxSurplus 0 ∧
        M.optsIn (M.maxSurplus 0) 0 = {0})) ∧
    (M.maxSurplus 0 ≤ M.maxSurplus 1 →
      M.oemProfit (M.maxSurplus 0) 0 = 2 * M.maxSurplus 0 ∧
      M.optsIn (M.maxSurplus 0) 0 = Finset.univ) ∧
    (M.maxSurplus 0 < M.maxSurplus 1 →
      M.oemProfit (M.maxSurplus 1) 0 = (M.w - M.c) * M.lam 0 + M.maxSurplus 1 ∧
      M.optsIn (M.maxSurplus 1) 0 = {1}) ∧
    ((∃ f r : ℝ, 0 ≤ f ∧ 0 ≤ r ∧ ∀ i, M.surplus i f r < 0) ∧
      ∀ f r : ℝ, (∀ i, M.surplus i f r < 0) →
        M.oemProfit f r = (M.w - M.c) * (M.lam 0 + M.lam 1) ∧ M.optsIn f r = ∅) ∧
    (∀ w' : ℝ, M.w ≤ w' → ∀ v v' : ℝ,
      IsLUB M.validProfits v → IsLUB (M.withW w').validProfits v' → v ≤ v') := by sorry

end IPLicense3D.Pooling
