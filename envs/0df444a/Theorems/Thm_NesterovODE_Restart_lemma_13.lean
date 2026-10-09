-- Prove2me | Theorems.Thm_NesterovODE_Restart_lemma_13
-- name    : NesterovODE.Restart.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:38:59.685738+00:00
-- url     : https://prove2.me/theorems/97f9086d-05f7-4453-94d1-d4f90f882ac1
-- title:
--   Lemma 13, p. 24 — a universal C̃ with T ≤ 4 exp(C̃L/µ)/(5√L)
-- statement:
--   There is a universal constant $\tilde C$ with the following property. Let $0<\mu\le L$, let $f\in\mathcal S_{\mu,L}$ with minimizer $x^\star$, let $x_0\ne x^\star$, and let $X$ solve (3) from $x_0$. Then the speed restarting time satisfies
--
--   $$T\le\frac{4\exp(\tilde CL/\mu)}{5\sqrt L}.$$
--
--   The lemma ensures that restarts happen often enough: within time $t$ at least $\lfloor5t\sqrt L\,e^{-\tilde CL/\mu}/4\rfloor$ restarts occur, which is what turns the per-restart decrease of Lemma 12 into linear convergence.
--
--   **Formalization Note** The bound is stated for every element $t$ of the set $\{t>0:\forall u\in(0,t),\ \mathrm d\|\dot X(u)\|^2/\mathrm du>0\}$ whose supremum is $T$. This is equivalent to the paper's bound and in addition says that the set is bounded, so $T$ is finite; a bound on Lean's `sSup` alone would hold vacuously for an unbounded set, whose `sSup` is $0$. $\tilde C$ is chosen before $n$, $f$, $\mu$, $L$, $x_0$ and the trajectory. The hypothesis $x_0\ne x^\star$ is the convention of §5.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 24, Lemma 13

import Mathlib
import Definitions.Def_NesterovODE_Restart_Setting

namespace NesterovODE.Restart

open scoped RealInnerProductSpace

/-- Lemma 13 (p. 24): there is a universal constant `C̃` (chosen before the dimension, `f`,
`μ`, `L`, `x₀`) with `T ≤ 4 exp(C̃L/μ)/(5√L)`, stated as a bound on every element of the
set whose supremum is `T` (so that set is bounded and `T` finite). Convention: `x₀ ≠ x⋆`. -/
theorem lemma_13 :
    ∃ Ct : ℝ,
      ∀ (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (μ : ℝ) (L : NNReal),
        0 < μ → μ ≤ L → NesterovODE.StrongCvx.InSMuL μ L f →
        ∀ (x₀ xstar : NesterovODE.WellPosed.E n), (∀ y, f xstar ≤ f y) → x₀ ≠ xstar →
        ∀ (X V : ℝ → NesterovODE.WellPosed.E n), NesterovODE.StrongCvx.IsSolution f 3 x₀ X V →
          ∀ t ∈ restartSet f X V, t ≤ 4 * Real.exp (Ct * L / μ) / (5 * Real.sqrt L) := by sorry

end NesterovODE.Restart
