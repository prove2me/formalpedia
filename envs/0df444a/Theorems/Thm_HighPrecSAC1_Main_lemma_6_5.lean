-- Prove2me | Theorems.Thm_HighPrecSAC1_Main_lemma_6_5
-- name    : HighPrecSAC1.Main.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:29:01.872562+00:00
-- url     : https://prove2.me/theorems/b0dd96b0-901f-4395-9e32-e67f3d874f41
-- title:
--   Lemma 6.5 — quadratic contraction
-- statement:
--   Assume (6.3) for a layered positive quadratic system, and let $\alpha,\beta\ge0$ satisfy $X-y\le\alpha X$ and $EX\le\beta X$. Write $H=2^{K+1}-1$ and perform update (6.4). Then
--   $$X-y'\le\alpha'X,\qquad E'X\le\beta'X,\qquad
--   \alpha'=H(\alpha^2+\beta\alpha),\quad\beta'=(\beta+2H\alpha)^2.$$
--   In addition, for $\zeta=\max\{H^2\alpha,H\beta\}$ and $\zeta'=\max\{H^2\alpha',H\beta'\}$,
--   $$\zeta'\le9\zeta^2.$$
--   The exact constant $9$ and both contraction bounds are part of the assertion.
--
--   Differences from the source:
--   - encoding: finite circuits, Boolean strings, vectors and entrywise matrix inequalities → Fin-indexed words and gates, real vectors, and the explicit EntryLE matrix relation; reason: these carriers preserve the finite objects and the componentwise order
--   - generalization: the scaled circuit system in Section 6.2 → any layered quadratic system with nonnegative coefficients, including zero width and depth where permitted; reason: the circuit system is an instance; the displayed identities use only positivity, degree at most two, and layered dependencies
--   - encoding: a nonnegative fixed point X of the layered global map → X is computed by layer evaluation from the initial block; reason: a strictly layered system has this unique fixed point, so no instance is excluded
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Lemma 6.5, printed p. 31 (PDF 32)

import Definitions.Def_HighPrecSAC1_Main_Refinement

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

theorem lemma_6_5 :
    ∀ (K m : ℕ) (S : LayerSystem K m) (T : RefState K m) (a b : ℝ),
    S.positive → Invariants S T → 0 ≤ a → 0 ≤ b →
    S.exact-T.y ≤ a • S.exact → T.E.mulVec S.exact ≤ b • S.exact →
    let ap := H K*(a^2+b*a)
    let bp := (b+2*H K*a)^2
    S.exact-(refine S T).y ≤ ap • S.exact ∧
    (refine S T).E.mulVec S.exact ≤ bp • S.exact ∧
    max ((H K)^2*ap) (H K*bp) ≤ 9*(max ((H K)^2*a) (H K*b))^2 := by sorry

end HighPrecSAC1.Main
