-- Prove2me | Theorems.Thm_LinearMDPRL_Linear_lemma_B_2
-- name    : LinearMDPRL.Linear.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:44.947905+00:00
-- url     : https://prove2.me/theorems/f2ad23f9-655e-41a6-97e8-f5963419f084
-- title:
--   Lemma B.2, p. 16 — the weight of Algorithm 1 satisfies ‖w^k_h‖ ≤ 2H√(dk/λ)
-- statement:
--   Consider Algorithm 1 run with regularization $\lambda>0$ and any bonus parameters on arbitrary data $(x^\tau_h,a^\tau_h)$, with features satisfying $\|\phi(x,a)\|\le1$. Fix $(k,h)\in[K]\times[H]$ and suppose that the regression targets are bounded by $2H$:
--   $$
--   \big|r_h(x^\tau_h,a^\tau_h)+\max_a Q^k_{h+1}(x^\tau_{h+1},a)\big|\le 2H\qquad\text{for }\tau=1,\dots,k-1.
--   $$
--   Then the weight $w^k_h$ computed in line 5 of Algorithm 1 satisfies
--   $$
--   \|w^k_h\|\le 2H\sqrt{dk/\lambda}.
--   $$
--
--   Together with Lemma D.6, this bound places the estimates $V^k_h$ in a function class of controlled covering number, which is how the concentration of Lemma B.3 is obtained.
--
--   **Formalization Note.** The proof on p. 16 bounds each regression target by $2H$. Algorithm 1 clips $Q^k_{h+1}$ only from above (at $H$), so this bound is not automatic for arbitrary data; it holds, for instance, when $Q^k_{h+1}\ge 0$. It is therefore stated as the hypothesis on the targets that the proof uses.
-- source:
--   Jin, Yang, Wang, Jordan, arXiv:1907.05388v2, Lemma B.2, p. 16 (target bound from its proof made explicit)

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB

namespace LinearMDPRL.Linear

open MeasureTheory ProbabilityTheory

/-- **Lemma B.2** (Bound on Weights in Algorithm; arXiv:1907.05388v2, p. 16). For any
`(k, h) ∈ [K] × [H]`, the weight `w^k_h` of Algorithm 1 satisfies `‖w^k_h‖ ≤ 2H√(dk/λ)`.

The bound `|r_h(x^τ_h, a^τ_h) + max_a Q^k_{h+1}(x^τ_{h+1}, a)| ≤ 2H` on the regression targets,
which the proof on p. 16 uses, is stated as the hypothesis `htarget`. -/
theorem lemma_B_2 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
    [Nonempty A] (d H K : ℕ) (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (hφ : ∀ x a, ‖φ x a‖ ≤ 1) (lam : ℝ) (hlam : 0 < lam) (β : ℕ → ℝ)
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) (hk : k ∈ Finset.Icc 1 K)
    (hh : h ∈ Finset.Icc 1 H)
    (htarget : ∀ τ ∈ Finset.Ico 1 k,
      |M.r h (xs τ h) (as τ h) + lsviV φ M.r lam β H xs as k (h + 1) (xs τ (h + 1))| ≤ 2 * H) :
    ‖lsviW φ M.r lam β H xs as k h‖ ≤ 2 * H * Real.sqrt (d * k / lam) := by sorry

end LinearMDPRL.Linear
