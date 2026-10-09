-- Prove2me | Theorems.Thm_MHSpectralGap_GlobalLip_proposition_2_6
-- name    : MHSpectralGap.GlobalLip.proposition_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:33.440525+00:00
-- url     : https://prove2.me/theorems/498c9738-198a-4229-9f3d-c85a58e51d61
-- title:
--   Proposition 2.6: weak Harris contraction and uniqueness
-- statement:
--   **Cited, not proved in this paper.** For a Markov kernel $P$ on a Polish space, suppose $V$ satisfies a Lyapunov estimate with constants $l,K$, a bounded distance-like function $d$ contracts with constant $c$, and the level set $\{V\le4K\}$ is $d$-small with constant $s$. Then an iteration count $\widetilde n$ depending only on these constants satisfies, for all probability measures $\nu_1,\nu_2$,
--
--   $$W_{\widetilde d}(\nu_1P^{\widetilde n},\nu_2P^{\widetilde n})\le\tfrac12W_{\widetilde d}(\nu_1,\nu_2),\qquad \widetilde d(x,y)=\sqrt{d(x,y)(1+V(x)+V(y))}.$$
--
--   In particular, at most one invariant probability measure exists. This result is the abstract step converting the paper's pCN estimates into a spectral gap.
--
--   **Formalization Note** The iteration count is quantified before the Polish space and the kernel, giving the dimension uniform dependence used in Theorem 2.12. The cited proposition's final Feller existence clause is not included here; existence of the pCN target invariant measure is stated in the goal. The Lyapunov function is assumed measurable, which the page presupposes when it integrates $V$ in (2.2); without it Lean's lower integral would not be the page's $P^nV$. The page's remark that $\widetilde n(l,K,c,s)$ is increasing in its arguments is not stated separately: its use in the paper is the bound $\widetilde n(m)\le\widetilde n$ for constants uniform in $m$, which the uniform choice of $\widetilde n$ gives directly.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, pp. 9–10, Proposition 2.6 (citing Hairer, Mattingly and Scheutzow 2011)

import Mathlib
import Definitions.Def_MHSpectralGap_GlobalLip_Wasserstein

namespace MHSpectralGap.GlobalLip

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Proposition 2.6, the weak Harris theorem, with uniform dependence on l,K,c,s. -/
theorem proposition_2_6 :
    ∀ l K c s : ℝ, ∃ ñ : ℕ,
      ∀ (E : Type) [MetricSpace E] [CompleteSpace E]
        [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
        (P : Kernel E E) [IsMarkovKernel P] (V : E → ℝ) (d : E → E → ℝ),
        Measurable V → IsLyapunov P V l K → IsDistanceLike d →
        (∀ x y, d x y ≤ 1) → IsDContracting P d c →
        IsDSmall P d {x | V x ≤ 4 * K} s →
          (∀ ν₁ ν₂ : Measure E,
            IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
            wass (dTilde d V) (ν₁.bind (P ^ ñ : Kernel E E))
              (ν₂.bind (P ^ ñ : Kernel E E)) ≤
              (1 / 2 : ℝ≥0∞) * wass (dTilde d V) ν₁ ν₂) ∧
          (∀ π₁ π₂ : Measure E,
            IsProbabilityMeasure π₁ → IsProbabilityMeasure π₂ →
            P.Invariant π₁ → P.Invariant π₂ → π₁ = π₂) := by sorry

end MHSpectralGap.GlobalLip
