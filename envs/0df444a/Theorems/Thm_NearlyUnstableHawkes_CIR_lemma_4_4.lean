-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_CIR_lemma_4_4
-- name    : NearlyUnstableHawkes.CIR.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:03.040848+00:00
-- url     : https://prove2.me/theorems/bc915d5f-4a2d-4e71-b326-b7b3caacee6e
-- title:
--   Lemma 4.4 — uniform Fourier decay of the rescaled resolvent
-- statement:
--   Suppose $a_T\to1$, $T(1-a_T)\to\lambda>0$, and $\phi$ satisfies Assumption 1. Let $\rho^T(x)=T\psi^T(Tx)/\|\psi^T\|_1$. A constant $c>0$, independent of $T$ and $z$, satisfies
--
--   $$|\widehat\rho^T(z)|\le c\min\{1,1/|z|\},\qquad T\ge1,$$
--
--   with the right side read as $c$ at $z=0$. This bound supplies an integrable domination for the next density convergence result.
--
--   **Formalization Note** $T$ runs through the positive sequence of observation scales. The explicit value at zero avoids division by zero in Lean.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 16, Lemma 4.4

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_CIR_Setting

open MeasureTheory Filter Topology Set

namespace NearlyUnstableHawkes.CIR

/-- Lemma 4.4, p. 16: uniform Fourier decay for the resolvent densities. -/
theorem lemma_4_4 (T a : ℕ → ℝ) (φ φ' : ℝ → ℝ)
    (m lam : ℝ) (hTpos : ∀ n, 0 < T n)
    (ha0 : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1)
    (hT : Tendsto T atTop atTop) (ha : Tendsto a atTop (𝓝 1))
    (hlam : 0 < lam)
    (h3 : Tendsto (fun n => T n * (1 - a n)) atTop (𝓝 lam))
    (hφ : Assumption1 φ φ' m) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ T n → ∀ z : ℝ,
      ‖fourierPlus (rho (fun s => a n * φ s) (T n)) z‖ ≤
        c * (if z = 0 then 1 else min 1 (1 / |z|)) := by sorry

end NearlyUnstableHawkes.CIR
