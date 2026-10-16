-- Prove2me | Theorems.Thm_Fundraising_PartialCollab_proposition_4
-- name    : Fundraising.PartialCollab.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:15.858016+00:00
-- url     : https://prove2.me/theorems/c59ed873-9c66-4654-9eb2-5e21455e180c
-- title:
--   Proposition 4, p. 20 — partial-collaboration equilibria exist; utilities solve the KKT system (11), efforts are any Σ_{i≤k̄} x_i = α^p_1 with x_i = 0 beyond k̄
-- statement:
--   Consider the partial-collaboration fundraising game with $n \ge 1$ HOs under its standing hypotheses, and let $\alpha^p_i(s) = \min\left(\dfrac{B_i}{\delta_i(s_i)\theta^p_i(s)}, 1\right)$. Then:
--
--   1. **Existence.** The game has a pure Nash equilibrium.
--   2. **Characterization.** Let $(s, x)$ be a profile with $s_i \in [a_i, b_i]$, $x_i \in [0, 1]$, labelled so that $\alpha^p_1(s) \ge \alpha^p_2(s) \ge \dots \ge \alpha^p_n(s)$, and let $\bar k = \#\{i : \alpha^p_i(s) = \alpha^p_1(s)\}$. Then $(s, x)$ is a Nash equilibrium if and only if
--      - (i) for every HO $i$ there are Lagrange multipliers $\lambda^p_{i1}, \lambda^p_{i2} \ge 0$ with
--   $$\frac{\delta_i'(s_i)}{\delta_i(s_i)} + \frac{\partial \theta^p_i(s)/\partial s_i}{\theta^p_i(s)} + \lambda^p_{i1} - \lambda^p_{i2} = 0, \qquad \lambda^p_{i1}(a_i - s_i) = 0, \qquad \lambda^p_{i2}(s_i - b_i) = 0, \tag{11}$$
--      - (ii) and the efforts satisfy
--   $$\sum_{i=1}^{\bar k} x_i = \alpha^p_1(s), \qquad x_{\bar k+1} = \dots = x_n = 0 .$$
--
--   In partial collaboration the HOs compete on earmarking but share the cost of reaching donors. The result says that equilibrium earmarking is independent of the efforts, and that the HOs with the highest required funding relative to their unit performance fund the whole platform while the others free-ride.
--
--   **Formalization Note** The partial derivative $\partial\theta^p_i/\partial s_i$ is the derivative of $t \mapsto \theta^p_i(s \text{ with } s_i := t)$ at $s_i$ (Mathlib `deriv`); $\delta_i$ is differentiable around $[a_i, b_i]$ by the standing hypotheses, so no derivative is a junk value. The paper's "without loss of generality" relabelling is the hypothesis that $\alpha^p(s)$ is antitone in the (0-based) index; $\alpha^p_1$ is the value at index $0$, and $\bar k$ is the count of entries tied with it (the printed $\max\{i : \alpha^p_1 = \dots = \alpha^p_i > \alpha^p_{i+1}\}$ needs $\alpha^p_{n+1}$ when all tie; the count gives $n$, as the proof reads it). (11) as printed writes $\theta^p(s)$ for $\theta^p_i(s)$. The equilibrium is the lexicographic best response of problem (10) with the paper's tie-break, in the reading recorded in the `Setting` (own effort $x_i$, own cost $C_i(x_i)$); $B_i > 0$ and concavity of $\delta_i$ are disclosed standing hypotheses.
-- source:
--   Aflaki, Pedraza-Martinez, Competition and Collaboration on Fundraising for Short-Term Disaster Response: The Impact on Earmarking and Performance, SSRN 3705595 (version of December 2022), p. 20, Proposition 4 (display (11)); proof pp. S13–S14 (PDF 46–47)

import Mathlib
import Definitions.Def_Fundraising_PartialCollab_Setting

namespace Fundraising.PartialCollab

open Finset

/-- Proposition 4, p. 20: the partial-collaboration game has a pure Nash equilibrium; and for
every profile `(s, x)` in the strategy box whose `α^p(s)` is antitone in the HO index (the
paper's "without loss of generality" ordering), `(s, x)` is an equilibrium iff (i) every `s_i`
solves the KKT system (11) with multipliers `λ^p_{i1}, λ^p_{i2} ≥ 0`, and (ii) the first `k̄`
efforts sum to `α^p_1(s)` and the remaining efforts are zero, `k̄ = #{i : α^p_i(s) = α^p_1(s)}`
(0-based indices: `α^p_1` is the value at index `0`). -/
theorem proposition_4 {n : ℕ} [NeZero n] (G : Setting n) (hG : G.Standing) :
    (∃ s x : Fin n → ℝ, G.IsNE s x) ∧
    ∀ s x : Fin n → ℝ, G.InBox s x → Antitone (G.alpha s) →
      (G.IsNE s x ↔
        (∀ i : Fin n, ∃ μ₁ μ₂ : ℝ, 0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧
          deriv (G.δ i) (s i) / G.δ i (s i) +
              deriv (fun t => theta (Function.update s i t) i) (s i) / theta s i +
              μ₁ - μ₂ = 0 ∧
          μ₁ * (G.a i - s i) = 0 ∧
          μ₂ * (s i - G.b i) = 0) ∧
        (∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < kbar (G.alpha s)), x i =
            G.alpha s 0) ∧
        ∀ i : Fin n, kbar (G.alpha s) ≤ (i : ℕ) → x i = 0) := by sorry

end Fundraising.PartialCollab
