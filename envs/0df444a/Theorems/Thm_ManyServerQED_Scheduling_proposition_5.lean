-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_proposition_5
-- name    : ManyServerQED.Scheduling.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:04:19.011525+00:00
-- url     : https://prove2.me/theorems/39813a1b-b969-4b3e-a4ab-d6e2e8b9ec03
-- title:
--   Proposition 5(i)–(ii) — the value function has polynomial growth and is continuous
-- statement:
--   Let $(\ell,\mu,\theta,r)$ be diffusion data and $\gamma>0$. Assume the running cost $L$ is continuous on $\mathbb R^k\times\mathbb S^k$ and satisfies Assumption 2(i), (iii) and (iv), with exponents $\varrho\in(0,1)$ and $m_L\ge0$. Then:
--   1. there is a constant $c$ such that
--   $$
--   V(x)\le c\,(1+\|x\|^{m_L}),\qquad x\in\mathbb R^k;
--   $$
--   2. $V$ is continuous on $\mathbb R^k$.
--
--   Growth and continuity of $V$ are what the existence proof of the HJB solution (Theorem 3) needs as boundary data.
--
--   **Formalization Note** $V$ takes values in $[0,\infty]$, and part 2 is continuity for the topology of $[0,\infty]$; by part 1, $V$ is finite. Part (iii) of Proposition 5 (the principle of optimality on smooth bounded domains) is not formalized.
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), pp. 25-26, Proposition 5(i)-(ii)

import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

/-- Proposition 5(i)–(ii) (pp. 25–26): if `L` is continuous and satisfies Assumption 2(i), (iii),
(iv) (with exponents `ϱ`, `m_L`), then (i) `V(x) ≤ c(1 + ‖x‖^{m_L})` for some constant `c` and all
`x`, and (ii) `V` is continuous on `ℝ^k`. -/
theorem proposition_5 {k : ℕ} [NeZero k] (D : DiffusionData k) (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (ϱ mL γ : ℝ) (hγ : 0 < γ) (hL : CostAssumptions L ϱ mL) :
    (∃ c : ℝ, ∀ x, value D L γ x ≤ ENNReal.ofReal (c * (1 + l1norm x ^ mL))) ∧
      Continuous (value D L γ) := by sorry

end ManyServerQED.Scheduling
