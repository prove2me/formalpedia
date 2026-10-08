-- Prove2me | Theorems.Thm_GenCMu_HeavyTraffic_proposition_4
-- name    : GenCMu.HeavyTraffic.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:37.046267+00:00
-- url     : https://prove2.me/theorems/b3461440-9276-4834-9956-3bc8905d40e9
-- title:
--   Proposition 4 (Little's law) — scaled delay averages over arrivals in $(na,nb]$ match time averages of $\tilde N^n_k$
-- statement:
--   Let $(Q^n)$ be a heavy-traffic sequence satisfying Assumption 1, let $T^n$ be feasible work-conserving policies, let $k$ be a class and $0 \le a < b \le 1$. Then
--   $$\frac{n^{-3/2}}{\bar A^n_k(b) - \bar A^n_k(a)}\int_{na}^{nb}\tau^n_k\,dA^n_k - \frac{1}{\bar A^n_k(b) - \bar A^n_k(a)}\int_a^b \tilde N^n_k(t)\,dt \to 0 \qquad (37),$$
--   where $\int_{na}^{nb}\tau^n_k\,dA^n_k = \sum\{\tau^n_k(U^n_k(i)) : na < U^n_k(i) \le nb\}$ is the sum of the delays of the class-$k$ jobs arriving in $(na, nb]$.
--
--   The average delay per arriving job and the time-average headcount are linked as in Little's law, at the diffusion scale and over every window.
--
--   **Formalization Note** The paper states (37) for $a,b\in[0,1]$, $a<b$; the post-horizon allocation condition controls the delays through $b=1$. The denominators are positive since $\bar A^n_k$ is strictly increasing.
--
--   The added `PostHorizonRegular` hypothesis requires $T^n_k(n+s\sqrt n)-T^n_k(n)=\rho_k(1)s\sqrt n+o(\sqrt n)$ uniformly for bounded $s\ge0$. It supplies the service behavior that the paper leaves unspecified after $n$.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), p. 819, Proposition 4 (Little's law), (37)

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits

namespace GenCMu.HeavyTraffic

open Filter Topology Finset


/-- Proposition 4 (Little's law), (37) (p. 819), for `0 ≤ a < b ≤ 1`. The Stieltjes integral
`∫_{na}^{nb} τⁿ_k dAⁿ_k` is the sum of the delays of the class-`k` jobs arriving in `(na, nb]`. -/
theorem proposition_4 {d : ℕ} (H : HTSeq d) (M : Limits d) (h1 : MainConvergence H M) (T : ℕ → Alloc d) (hT : ∀ n, (H.Q n).IsFeasible (T n)) (hpost : PostHorizonRegular H M T) (k : Fin d) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun n : ℕ =>
      ((n : ℝ) ^ (-(3 / 2 : ℝ)) / (H.Abar n b k - H.Abar n a k)) *
          ∑ i ∈ Finset.Ioc ((H.Q n).A k (n * a)) ((H.Q n).A k (n * b)),
            (H.Q n).delay (T n) k ((H.Q n).U k i)
        - (1 / (H.Abar n b k - H.Abar n a k)) * ∫ t in a..b, H.Nt T n t k)
      atTop (𝓝 0) := by sorry
end GenCMu.HeavyTraffic
