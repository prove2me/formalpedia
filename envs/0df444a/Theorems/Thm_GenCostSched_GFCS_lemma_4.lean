-- Prove2me | Theorems.Thm_GenCostSched_GFCS_lemma_4
-- name    : GenCostSched.GFCS.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:58.214286+00:00
-- url     : https://prove2.me/theorems/820f78fe-0d0b-497e-bdb3-49fefff8e211
-- title:
--   Lemma 4, p. 16 — the new optimal dual β′ dominates the old β: β′_t ≥ β_t for t ≥ r_n
-- statement:
--   At the arrival of job $n$ at time $s=r_n$, let $\mathrm{RNF}(r_n)$ be the identical-release instance of the alive jobs $A$ (released no later than $s$, positive lengths $\rho_j$). Let $\mathrm{RNF}'(r_n)$ be the same instance with job $n$ added ($r_n=s$, length $v_n$). Let $(\alpha,\beta)$ be any optimal solution of the dual (2) of $\mathrm{RNF}(r_n)$. Let $(\alpha',\beta')$ be any optimal solution of the dual of $\mathrm{RNF}'(r_n)$. Then
--   $$\beta'_t\ \ge\ \beta_t\qquad\text{for almost every } t\ge r_n .$$
--
--   Lemma 5 rests on this monotonicity: the new tail of the β-variable dominates the old one, so the α-variables already set stay feasible after the dual update of Algorithm 2.
--
--   **Formalization Note.** Dual variables are per unit length and $\beta$ is an integrable density, so the inequality is stated almost everywhere. The statement is posed, as printed, for every pair of optimal duals of the continuous linear programs of Definition 3. The proof (p. 17) works in a time-discretized model and picks the optimal $\beta'$ with the largest $\sum_t\beta'_t$; in the discretized model that choice matters, but in the continuous model with continuous cost functions the optimal dual is unique up to null sets, so no choice is needed.
--
--   Differences from the source:
--
--   - generalization: the instance RNF(r_n)/RNF′(r_n) met by Algorithm 2 at the arrival of job n (alive jobs A(r_n), residual lengths) → every identical-release instance GFCS(s) of jobs A with r_j ≤ s and positive lengths ρ_j, plus a new job k with r_k = s and length v_k; reason: every arrival of Algorithm 2 is such an instance (A = A(r_n), ρ = residual lengths), so the statement specializes to the paper's
--   - encoding: the proof works with the Δ-discretized, scaled RNF(r_n) of Remark 2 (p. 16) → the continuous LPs RNF(r_n), RNF′(r_n) of Definition 3, with ∀ t ≥ r_n read as almost every t ≥ r_n; reason: Lemma 4 cites the linear programs of Definition 3, which are continuous; the discretization is a proof device and β is an L¹ density; in the continuous LPs with continuous g the optimal dual is unique up to null sets, so the discrete-slot instance on which the literal statement fails for a non-maximal β′ (paper.md) has no continuous analogue, and the statement is posed for every optimal pair, at full strength
--   - encoding: dual (2): α_j/v_j ≤ β_t + g_j(t) for all t ≥ r_j, α_j, β_t ≥ 0 → per-unit variables a_j = α_j/v_j (residual length for GFCS(s)); β integrable on the horizon; β ≥ 0 and the constraints hold for almost every t; reason: β is a density on the time axis: changing it on a null set changes no dual objective; the pointwise form would make optimal duals ill-defined
-- source:
--   Etesami, An Optimal Control Framework for Online Job Scheduling with General Cost Functions, arXiv:1906.02644v3, p. 16, Lemma 4

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model

open MeasureTheory Set
open scoped ENNReal

namespace GenCostSched.GFCS

/-- Lemma 4 (p. 16): for every optimal dual `(a, β)` of `RNF(s)` (jobs `A`) and every optimal
dual `(a′, β′)` of `RNF′(s)` (jobs `A ∪ {k}`, the new job `k` released at `s`),
`β′_t ≥ β_t` for a.e. `t ≥ s`. -/
theorem lemma_4 {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (k : Fin m) (hk : k ∉ A) (hA : ∀ j ∈ A, I.r j ≤ s)
    (hrk : I.r k = s) (hρ : ∀ j ∈ A, 0 < ρ j) (hρk : ρ k = I.v k)
    (a : Fin m → ℝ) (β : ℝ → ℝ) (hold : IsOffOptDual I.g s A ρ a β)
    (a' : Fin m → ℝ) (β' : ℝ → ℝ) (hnew : IsOffOptDual I.g s (insert k A) ρ a' β') :
    ∀ᵐ t, s ≤ t → β t ≤ β' t := by sorry

end GenCostSched.GFCS
