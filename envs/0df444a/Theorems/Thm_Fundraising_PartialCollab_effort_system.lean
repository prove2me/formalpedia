-- Prove2me | Theorems.Thm_Fundraising_PartialCollab_effort_system
-- name    : Fundraising.PartialCollab.effort_system
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:14.105986+00:00
-- url     : https://prove2.me/theorems/4bde8718-773d-4363-892b-998df83fa78f
-- title:
--   Proposition 4(ii), p. 20 — the effort system x_i = (α_i − Σ_{j≠i} x_j)^+ is solved exactly by Σ_{i≤k̄} x_i = α_1, x_i = 0 beyond k̄
-- statement:
--   Let $1 \ge \alpha_1 \ge \alpha_2 \ge \dots \ge \alpha_n \ge 0$ ($n \ge 1$), and let
--   $$\bar k = \#\{i : \alpha_i = \alpha_1\}$$
--   be the number of entries tied with the largest one, so that $\alpha_1 = \dots = \alpha_{\bar k} > \alpha_{\bar k + 1}$. For efforts $x \in [0, 1]^n$ the following are equivalent:
--   1. $x$ solves the effort system $x_i = \left(\alpha_i - \sum_{j \ne i} x_j\right)^+$ for every $i$;
--   2. $$\sum_{i=1}^{\bar k} x_i = \alpha_1 \quad\text{and}\quad x_{\bar k + 1} = \dots = x_n = 0 .$$
--
--   Applied to $\alpha_i = \alpha^p_i(s^p)$, this is part (ii) of Proposition 4: only the HOs with the largest required-funding index contribute effort, and the others free-ride.
--
--   **Formalization Note** Indices are $0$-based in Lean: $\alpha_1$ is `α 0`, and the first $\bar k$ entries are those of index `< kbar α`. The paper's $\bar k = \max\{i : \alpha_1 = \dots = \alpha_i > \alpha_{i+1}\}$ needs an $\alpha_{n+1}$ when all entries tie; the count used here gives $\bar k = n$ then, as the paper's proof reads it. "Any solution" ranges over $x \in [0,1]^n$. $0 \le \alpha^p_i \le 1$ follows from its definition and the positive model parameters; nonnegativity is needed because, with $\alpha_1 < 0$, $x = 0$ solves the system but not condition 2.
-- source:
--   Aflaki, Pedraza-Martinez, Competition and Collaboration on Fundraising for Short-Term Disaster Response: The Impact on Earmarking and Performance, SSRN 3705595 (version of December 2022), p. 20, Proposition 4(ii); proof p. S14 (PDF 47)

import Mathlib
import Definitions.Def_Fundraising_PartialCollab_Setting

namespace Fundraising.PartialCollab

open Finset

/-- Proposition 4(ii), p. 20 (proof p. S14), as a statement about the effort system: for
`1 ≥ α_0 ≥ α_1 ≥ ⋯ ≥ α_{n-1} ≥ 0` and `x ∈ [0, 1]^n`, the efforts solve
`x_i = (α_i − Σ_{j ≠ i} x_j)^+` for every `i` iff the first `k̄` efforts sum to `α_0` and the
remaining efforts are zero, where `k̄ = #{i : α_i = α_0}`. -/
theorem effort_system {n : ℕ} [NeZero n] (α x : Fin n → ℝ) (hα : Antitone α)
    (hα_nonneg : ∀ i, 0 ≤ α i) (hα_le_one : ∀ i, α i ≤ 1)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    (∀ i, x i = max (α i - ∑ j ∈ univ.erase i, x j) 0) ↔
      (∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < kbar α), x i = α 0) ∧
      ∀ i : Fin n, kbar α ≤ (i : ℕ) → x i = 0 := by sorry

end Fundraising.PartialCollab
