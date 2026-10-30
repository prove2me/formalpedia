-- Prove2me | Theorems.Thm_GenCostSched_GFCS_weak_duality_21
-- name    : GenCostSched.GFCS.weak_duality_21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:37.389639+00:00
-- url     : https://prove2.me/theorems/1175ee0a-0c60-4e04-a9b1-706eec5b0009
-- title:
--   §IV, p. 21 — a feasible solution of the dual (2) is feasible for the dual of the slower LP (21), and its objective is at most OPT_{1/(1+ε)}
-- statement:
--   Let an online GFCS instance satisfy the standing assumptions of §II. Let $(\alpha,\beta)$ be feasible for the dual (2) of LP (1), written per unit length $a_j=\alpha_j/v_j$:
--   $a_j\ge 0$, $\beta_t\ge 0$, $\beta$ integrable on $[0,\infty)$, and $a_j\le\beta_t+g_j(t)$ for almost every $t\ge r_j$. The dual of the slower LP (21) has the same constraints, so $(\alpha,\beta)$ is feasible for it too. Weak duality then says that for every machine capacity $c>0$,
--   $$\sum_j \alpha_j-c\int_0^\infty\beta_t\,dt\;\le\;\mathrm{OPT}_c,$$
--   where $\mathrm{OPT}_c$ is the optimal value of LP (1) with $\sum_jx_j(t)\le c$. The case $c=1/(1+\epsilon)$ is LP (21).
--
--   This is the weak duality the proof of Theorem 3 invokes at its last step (p. 22) to compare the cost of Algorithm 2 with the slower offline benchmark.
--
--   **Formalization Note.** Since $\mathrm{OPT}_c$ is valued in $[0,\infty]$, the left side enters as its positive part `ENNReal.ofReal`. That changes nothing, because $\mathrm{OPT}_c\ge 0$.
--
--   Differences from the source:
--
--   - generalization: machine capacity 1/(1+ε) of (21) → every capacity c > 0; reason: c = 1/(1+ε) is LP (21) and c = 1 is LP (1); the statement specializes to both
--   - reading: feasibility for the dual of (21) (p. 21) and 'Using weak duality' (p. 22) → one statement: ofReal(Σ_j α_j − c ∫_0^∞ β) ≤ OPT_c; reason: the passage asserts feasibility; the use it is put to on p. 22 is weak duality, so both are posed together
--   - reading: the dual of (21) prints α_j/v_j ≤ β_t + ρ_j g(t) → a_j ≤ β_t + g_j(t), the constraint of (2); reason: p. 21: 'as they both share the same constraints'; ρ_j g is a leftover from (3)
--   - encoding: dual (2): α_j/v_j ≤ β_t + g_j(t) for all t ≥ r_j, α_j, β_t ≥ 0 → per-unit variables a_j = α_j/v_j (residual length for GFCS(s)); β integrable on the horizon; β ≥ 0 and the constraints hold for almost every t; reason: β is a density on the time axis: changing it on a null set changes no dual objective; the pointwise form would make optimal duals ill-defined
--   - encoding: real-valued LP objectives and optimal values → costs, OPT_c and RNF are lintegrals in ℝ≥0∞ of ENNReal.ofReal of the integrand; reason: the integrand g_j(t) x_j(t) is nonnegative on every schedule (x_j vanishes before r_j, where g_j ≥ 0), so nothing changes, and no non-integrable schedule can get the junk cost 0
-- source:
--   Etesami, An Optimal Control Framework for Online Job Scheduling with General Cost Functions, arXiv:1906.02644v3, p. 21, remark after (21) ('any feasible dual solution … will also be feasible to the dual of the slower system (21)'), and proof of Theorem 3, p. 22 ('Using weak duality')

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model

open MeasureTheory Set
open scoped ENNReal

namespace GenCostSched.GFCS

/-- Weak duality for LP (1) with machine capacity `c` (LP (21) for `c = 1/(1+ε)`, p. 21): a
feasible solution of the dual (2) is feasible for the dual of the slower system, and its dual
objective `∑_j α_j − c ∫_0^∞ β_t dt` is at most `OPT_c`. -/
theorem weak_duality_21 {n : ℕ} (I : Instance n) (hI : I.Standing) (a : Fin n → ℝ) (β : ℝ → ℝ)
    (hfeas : I.IsDualFeas a β) (c : ℝ) (hc : 0 < c) :
    ENNReal.ofReal (I.dualObj c a β) ≤ I.optLP c := by sorry

end GenCostSched.GFCS
