-- Prove2me | Theorems.Thm_MDPFinance_DividendProblems_lemma_9_2_2
-- name    : MDPFinance.DividendProblems.lemma_9_2_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:13:19.46098+00:00
-- url     : https://prove2.me/theorems/98f89a2d-f008-470f-ab6f-ef6e45145dd3
-- title:
--   Lemma 9.2.2 — the dividend model's bounding function
-- statement:
--   This lemma establishes the Convergence Assumption (C) for the dividend model by exhibiting an explicit bounding function $b(x):=1+x$ ($x\ge0$), $b(x):=0$ ($x<0$), with an explicit bound $T_\circ^nb \le \beta^nb+n\,\mathbb EZ^+$ on the shifted-value operator's growth, and derives from it the concrete bound $\delta(x)\le x+\beta\,\mathbb EZ^+/(1-\beta)$ on the Integrability Assumption's own bound $\delta$ — which, for this positive-reward model, coincides with $J_\infty$ itself. This is the technical foundation every later result in §9.2 builds on.
--
--   **Moderation note.** The draft asserted that `b` is a bounding function with constant `α_b = 1`, which is false (for `Z = 2` w.p. `0.9`, `−1` w.p. `0.1`: `∫ b dQ(·|0,0) = 2.7 > b(0) = 1`); the book fixes no constant. Now `∃ c_r α_b`. The bound `T_∘^n b ≤ β^n b + n𝔼Z⁺` is stated with the `[0,∞]`-valued shift operator (no junk integrals), and b) is `J_∞(x) ≤ x + β𝔼Z⁺/(1−β)` for `x ≥ 0`, finiteness of `J_∞` everywhere and `J_∞ ∈ IB_b` (the book's `δ = J_∞` for this positive model).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 273, PDF 283, Lemma 9.2.2

import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter

namespace MDPFinance.DividendProblems

/-- Lemma 9.2.2 (Bäuerle–Rieder, p. 273, PDF 283). a) `b(x) := 1 + x` for `x \ge 0`, `b(x) := 0`
for `x < 0`, is a bounding function for the dividend model (for some constants `c_r, \alpha_b`),
with `T_\circ^n b \le \beta^n b + n\,\mathbb E Z^+`. b) For `x \ge 0`, `\delta(x) \le x + \beta\,
\mathbb E Z^+/(1-\beta)`, hence `\delta \in IB_b` — where `\delta = J_\infty` for this positive
model (the book's own remark in the proof), so `J_\infty` is finite everywhere and `b`-bounded. -/
theorem lemma_9_2_2 (M : DividendModel) :
    (∃ cr αb : ℝ, IsBoundingFunction M.toMDM
        (fun x : ℤ => if 0 ≤ x then 1 + (x : ℝ) else 0) cr αb) ∧
      (∀ n : ℕ, ∀ x : ℤ,
        (TcircL M.toMDM)^[n] (fun x : ℤ => ENNReal.ofReal (if 0 ≤ x then 1 + (x : ℝ) else 0)) x ≤
          ENNReal.ofReal (M.β ^ n * (if 0 ≤ x then 1 + (x : ℝ) else 0) + n * M.EZplus)) ∧
      (∀ x : ℤ, 0 ≤ x → M.Jinf x ≤ ENNReal.ofReal ((x : ℝ) + M.β * M.EZplus / (1 - M.β))) ∧
      (∀ x, M.Jinf x < ⊤) ∧
      (fun x => (M.Jinf x).toReal) ∈ IBb (fun x : ℤ => if 0 ≤ x then 1 + (x : ℝ) else 0) := by sorry

end MDPFinance.DividendProblems
