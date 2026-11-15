-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_Supplement_two_sided_concentration
-- name    : LinearHashingPoissonesque.ExpectedLoads.Supplement.two_sided_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:10:13.7487+00:00
-- url     : https://prove2.me/theorems/6b1aeeda-8923-415f-b7a7-7959b7d88984
-- title:
--   Theorem 4 (companion theorem; not used in the proof of the goal) — two-sided bin concentration
-- statement:
--   Let $u\ge\ell\ge1$, $n=2^\ell$, and let $S\subseteq\mathbb F_2^u$ have size $m>n\log n$. For every $0<\varepsilon<1$, a uniformly random linear map $h:\mathbb F_2^u\to\mathbb F_2^\ell$ satisfies
--
--   $$\Pr_h\!\left[\forall v\in\mathbb F_2^\ell:
--   \left|L_v(S,h)-\frac mn\right|\le5\sqrt{\frac{m\log n}{\varepsilon n}}\right]\ge1-\varepsilon.$$
--
--   All bins, including empty bins, occur inside the same event. This is Theorem 4 on page 5, restated as Corollary 3 on pages 20–21; the restatement is not a separate milestone.
--
--   Differences from the source:
--   - encoding: binary coordinate spaces and n = 2^ℓ → Fin u → ZMod 2 and Fin ℓ → ZMod 2, with n substituted as 2^ell; reason: these are exactly the source spaces and their cardinalities; ell is independent of the number of balls
--   - encoding: probability under a uniform random linear map → LinMaxLoad.probLin, the average of the event indicator over all linear maps; reason: the finite uniform law includes rank-deficient maps and imposes no surjectivity or affine shift
--   - encoding: the labelled load L_v and simultaneous two-sided bound → the published binLoad, cast to reals, and ∀ v inside probLin; reason: the count includes empty bins and absolute values retain both deviations
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.5, Theorem 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf#page=5

import Definitions.Def_LinMaxLoad_probLin
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_BinLoad

namespace LinearHashingPoissonesque.ExpectedLoads.Supplement

/-- Theorem 4, p.5 (= Corollary 3, pp.20–21): one event controls every labelled bin. -/
theorem two_sided_concentration {u ell m : ℕ} (hu : ell ≤ u) (hell : 1 ≤ ell)
    (S : Finset (Fin u → ZMod 2)) (hS : S.card = m)
    (hdense : (2 : ℝ) ^ ell * Real.log ((2 : ℝ) ^ ell) < m)
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1) :
    1 - eps ≤ LinMaxLoad.probLin (ZMod 2) (Fin u → ZMod 2) ell
      (fun h => ∀ v : Fin ell → ZMod 2,
        |(binLoad S h v : ℝ) - (m : ℝ) / (2 : ℝ) ^ ell| ≤
          5 * Real.sqrt ((m : ℝ) * Real.log ((2 : ℝ) ^ ell) /
            (eps * (2 : ℝ) ^ ell))) := by sorry

end LinearHashingPoissonesque.ExpectedLoads.Supplement
