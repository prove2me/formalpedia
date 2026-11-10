-- Prove2me | Theorems.Thm_HighPrecSAC1_Main_lemma_6_6
-- name    : HighPrecSAC1.Main.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:29:09.863817+00:00
-- url     : https://prove2.me/theorems/3fc0d50a-95b1-4870-af93-ddcaf3f87aa2
-- title:
--   Lemma 6.6 — the number of refinement rounds
-- statement:
--   Let $K,t\ge1$, $\tau=6K+20$, $H=2^{K+1}-1$, $\alpha_0=2\cdot4^K2^{-\tau}$ and $\beta_0=(K+1)2^{-\tau}H$. Suppose a layered positive quadratic system and an initial tuple satisfy (6.3), $X-y\le\alpha_0X$ and $EX\le\beta_0X$. Set
--   $$q=\min\{j\ge0:(2K+13)2^j\ge t+4\}.$$
--   One absolute constant bounds $q$ by $O(\log(2+t/K))$ for all $K,t\ge1$. After exactly $q$ updates (6.4),
--   $$0\le X-y^{(q)}\le2^{-t-4}X.$$
--   The minimum, exact round count, uniform asymptotic clause and final accuracy are all retained.
--
--   Differences from the source:
--   - encoding: finite circuits, Boolean strings, vectors and entrywise matrix inequalities → Fin-indexed words and gates, real vectors, and the explicit EntryLE matrix relation; reason: these carriers preserve the finite objects and the componentwise order
--   - generalization: the scaled circuit system in Section 6.2 → any layered quadratic system with nonnegative coefficients, including zero width and depth where permitted; reason: the circuit system is an instance; the displayed identities use only positivity, degree at most two, and layered dependencies
--   - encoding: a nonnegative fixed point X of the layered global map → X is computed by layer evaluation from the initial block; reason: a strictly layered system has this unique fixed point, so no instance is excluded
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Lemma 6.6, printed p. 32 (PDF 33)

import Definitions.Def_HighPrecSAC1_Main_Refinement

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

theorem lemma_6_6 :
    ∃ c : ℝ, 0 < c ∧ ∀ K t : ℕ, 1 ≤ K → 1 ≤ t →
    (roundCount K t : ℝ) ≤ c*lg (2+(t:ℝ)/K) ∧
    ∀ (m : ℕ) (S : LayerSystem K m) (T : RefState K m),
      S.positive → Invariants S T →
      S.exact-T.y ≤ alpha0 K • S.exact → T.E.mulVec S.exact ≤ beta0 K • S.exact →
      0 ≤ S.exact-(rounds S T (roundCount K t)).y ∧
      S.exact-(rounds S T (roundCount K t)).y ≤ err (t+4) • S.exact := by sorry

end HighPrecSAC1.Main
