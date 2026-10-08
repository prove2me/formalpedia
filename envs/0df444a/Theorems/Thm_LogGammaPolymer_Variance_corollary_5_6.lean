-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_corollary_5_6
-- name    : LogGammaPolymer.Variance.corollary_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:09.768977+00:00
-- url     : https://prove2.me/theorems/00992ca4-4d45-4772-b6e8-a8267de75f46
-- title:
--   Corollary 5.6 — Var[log Z_{m,n}] ≥ cN^{2/3} for large N
-- statement:
--   Assume (2.4) and rectangle dimensions (2.6). Then there exists a constant $c>0$ such that for large enough $N$,
--   $$\mathrm{Var}^\theta\bigl[\log Z_{m,n}\bigr]\ge cN^{2/3}.$$
--
--   This is the lower half of Theorem 2.1: the free energy in the characteristic direction fluctuates at least on the scale $N^{1/3}$.
--
--   **Formalization Note** The printed corollary says "a constant $c$" without requiring $c>0$, which would make the statement trivial ($c=0$). The intended $c>0$ is stated. "For large enough $N$" is an $N_0$ chosen together with $c$, before the environment, $N$, $m$ and $n$. $\gamma$ is an arbitrary real.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Corollary 5.6, p. 36

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem corollary_5_6 {θ μ : ℝ} (hθ : 0 < θ) (hθμ : θ < μ) (γ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (E : Env θ μ P) (N : ℝ), N₀ ≤ N → ∀ m n : ℕ, InRect θ μ γ N m n →
        c * N ^ ((2 : ℝ) / 3) ≤ variance (logZ E m n) P := by sorry

end LogGammaPolymer.Variance
