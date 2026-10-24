-- Prove2me | Theorems.Thm_GenCostSched_GFCS_dual_attainment
-- name    : GenCostSched.GFCS.dual_attainment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:45.51525+00:00
-- url     : https://prove2.me/theorems/5e2073ed-0a37-48f0-932b-0733ed3aac1d
-- title:
--   §III-A, p. 12, and proof of Lemma 4, p. 17 — GFCS(s) has an optimal dual with value RNF, and a maximal one (largest ∫β)
-- statement:
--   Consider an identical-release instance GFCS(s). Its jobs form a finite set $A$, each released no later than $s$ and satisfying the standing assumptions of §II, and job $j$ has length $\rho_j>0$ (in Algorithm 2, its residual length at time $s$). Let
--   $$\mathrm{RNF}=\inf\Big\{\sum_{j\in A}\int_s^\infty g_j(t)x_j(t)\,dt:\ \int_s^\infty x_j\ge\rho_j\ (j\in A),\ \sum_{j\in A}x_j(t)\le 1,\ x_j\ge 0\Big\}$$
--   be its optimal value (Definition 3). Then:
--
--   1. $\mathrm{RNF}$ is finite;
--   2. the dual (2) on $[s,\infty)$ has an optimal solution $(\alpha,\beta)$ with $\sum_{j\in A}\alpha_j-\int_s^\infty\beta_t\,dt=\mathrm{RNF}$ (strong duality with attainment);
--   3. this optimal solution can be chosen *maximal*: its $\int_s^\infty\beta_t\,dt$ is the largest among all optimal dual solutions.
--
--   Item 2 is what §III-A derives from the minimum principle: the costate curves give dual variables that are feasible, and hence optimal. Item 3 is the choice made in the proof of Lemma 4 ("we take $\beta'_t$ to be the maximal one"). Lemmas 4–6 and the dual update of Algorithm 2 rely on item 2.
--
--   **Formalization Note.** Dual variables are per unit length, $a_j=\alpha_j/\rho_j$. The dual constraints hold for almost every $t\ge s$ and $\beta$ is integrable on $[s,\infty)$. $\mathrm{RNF}$ is valued in $[0,\infty]$, and its finiteness is part of the statement.
--
--   Differences from the source:
--
--   - reading: the costates of the minimum principle define dual variables that are feasible and hence optimal; the proof of Lemma 4 takes the maximal optimal dual → RNF is finite, and there is an optimal dual (a, β) with objective RNF and the largest ∫_s^∞ β among optimal duals; reason: the costate construction is a proof device; what the later lemmas use is strong duality with attainment; the maximal dual is the object the proof of Lemma 4 works with
--   - encoding: the maximal dual has the largest Σ_{t ≥ r_n} β′_t (discrete slots) → the largest ∫_s^∞ β; reason: continuous form of the slot sum of the scaled RNF of Remark 2
--   - encoding: dual (2): α_j/v_j ≤ β_t + g_j(t) for all t ≥ r_j, α_j, β_t ≥ 0 → per-unit variables a_j = α_j/v_j (residual length for GFCS(s)); β integrable on the horizon; β ≥ 0 and the constraints hold for almost every t; reason: β is a density on the time axis: changing it on a null set changes no dual objective; the pointwise form would make optimal duals ill-defined
--   - encoding: real-valued LP objectives and optimal values → costs, OPT_c and RNF are lintegrals in ℝ≥0∞ of ENNReal.ofReal of the integrand; reason: the integrand g_j(t) x_j(t) is nonnegative on every schedule (x_j vanishes before r_j, where g_j ≥ 0), so nothing changes, and no non-integrable schedule can get the junk cost 0
-- source:
--   Etesami, An Optimal Control Framework for Online Job Scheduling with General Cost Functions, arXiv:1906.02644v3, p. 12 (§III-A, after (9): dual variables from costates are dual feasible and optimal), p. 17 (proof of Lemma 4: the maximal optimal dual)

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model

open MeasureTheory Set
open scoped ENNReal

namespace GenCostSched.GFCS

/-- Strong duality and dual attainment for GFCS(s) (§III-A, p. 12; proof of Lemma 4, p. 17):
for an identical-release instance the optimal value `RNF` is finite, the dual (2) has an optimal
solution whose objective equals `RNF`, and it can be chosen maximal, i.e. with the largest
`∫_s^∞ β` among all optimal dual solutions. -/
theorem dual_attainment {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s) (hρ : ∀ j ∈ A, 0 < ρ j) :
    rnf I.g s A ρ ≠ ⊤ ∧
      ∃ (a : Fin m → ℝ) (β : ℝ → ℝ), IsOffMaxOptDual I.g s A ρ a β ∧
        offDualObj s A ρ a β = (rnf I.g s A ρ).toReal := by sorry

end GenCostSched.GFCS
