-- Prove2me | Theorems.Thm_GenEmpLik_Coverage_lemma_17
-- name    : GenEmpLik.Coverage.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:04:30.781126+00:00
-- url     : https://prove2.me/theorems/77afa6be-d33e-44b1-98f0-0da693436ad1
-- title:
--   Lemma 17 — directional derivative of an optimal value
-- statement:
--   Let $F$ be a lower semicontinuous real objective on a nonempty closed decision set $\mathcal X$. Suppose some nonempty near-minimizer set $\{x\in\mathcal X:F(x)\le\inf_{\mathcal X}F+\varepsilon_0\}$ is compact. Let $H$ be continuous and bounded on $\mathcal X$, let each $H_n$ be bounded there, and suppose $\sup_{x\in\mathcal X}|H_n(x)-H(x)|\to0$. For positive $t_n\to0$, writing $S^\star=\arg\min_{\mathcal X}F$, one has
--
--   $$\frac{\inf_{x\in\mathcal X}\{F(x)+t_nH_n(x)\}-\inf_{x\in\mathcal X}F}{t_n}\longrightarrow\inf_{x\in S^\star}H(x).$$
--
--   This is the optimal-value directional derivative used to identify the influence function.
--
--   **Formalization Note** Signed measures are represented by their action $H(x)=\int\ell(x;z)\,dH(z)$ on the loss class. Positive $t_n$ follows the directional reading used in Appendix C.2.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 38, Lemma 17; proof pp. 39–40

import Mathlib

open Filter Topology

namespace GenEmpLik.Coverage

/-- Lemma 17, pp. 38–40, in the action of signed measures on the loss class. -/
theorem lemma_17 {E : Type*} [MetricSpace E]
    (X : Set E) (F H : E → ℝ) (Hn : ℕ → E → ℝ) (t : ℕ → ℝ)
    (hXclosed : IsClosed X) (hXnonempty : X.Nonempty)
    (hFlsc : LowerSemicontinuousOn F X)
    (hsublevel : ∃ ε₀ : ℝ, 0 < ε₀ ∧
      IsCompact {x | x ∈ X ∧ F x ≤ sInf (F '' X) + ε₀} ∧
      Set.Nonempty {x | x ∈ X ∧ F x ≤ sInf (F '' X) + ε₀})
    (hHcont : ContinuousOn H X)
    (hHbdd : BddAbove ((fun x => |H x|) '' X))
    (hHnbdd : ∀ n, BddAbove ((fun x => |Hn n x|) '' X))
    (htpos : ∀ n, 0 < t n) (htzero : Tendsto t atTop (𝓝 0))
    (hHn : Tendsto (fun n => ⨆ x : X, |Hn n x - H x|) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (sInf ((fun x => F x + t n * Hn n x) '' X) - sInf (F '' X)) / t n)
      atTop (𝓝 (sInf (H '' {x | x ∈ X ∧ F x = sInf (F '' X)}))) := by sorry

end GenEmpLik.Coverage
