-- Prove2me | Theorems.Thm_HighPrecSAC1_Main_lemma_6_4
-- name    : HighPrecSAC1.Main.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:29:29.664356+00:00
-- url     : https://prove2.me/theorems/1b8f8838-ae6e-45c5-813a-1918c7f37c7e
-- title:
--   Lemma 6.4 — preservation of refinement invariants
-- statement:
--   For a layered positive quadratic system with exact vector $X$, assume the four invariants (6.3): $0\le y\le X$, $r=\Phi(y)-y\ge0$, $R\ge0$, and $E=I-(I-J(y))R\ge0$. Perform exactly (6.4), including $s=Rr$, $B=E+DQ(s)R$, and $E'=B^2$. Then
--   $$0\le y\le y'\le\Phi(y')\le X,\quad
--   r'=\Phi(y')-y'\ge0,\quad R'\ge0,\quad
--   E'=I-(I-J(y'))R'\ge0.$$
--   All vector and matrix comparisons are entrywise. This asserts both the residual identities and preservation of nonnegativity.
--
--   Differences from the source:
--   - encoding: finite circuits, Boolean strings, vectors and entrywise matrix inequalities → Fin-indexed words and gates, real vectors, and the explicit EntryLE matrix relation; reason: these carriers preserve the finite objects and the componentwise order
--   - generalization: the scaled circuit system in Section 6.2 → any layered quadratic system with nonnegative coefficients, including zero width and depth where permitted; reason: the circuit system is an instance; the displayed identities use only positivity, degree at most two, and layered dependencies
--   - encoding: a nonnegative fixed point X of the layered global map → X is computed by layer evaluation from the initial block; reason: a strictly layered system has this unique fixed point, so no instance is excluded
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Lemma 6.4, printed p. 30 (PDF 31)

import Definitions.Def_HighPrecSAC1_Main_Refinement

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

theorem lemma_6_4 :
    ∀ (K m : ℕ) (S : LayerSystem K m) (T : RefState K m),
    S.positive → Invariants S T →
    let U := refine S T
    0 ≤ T.y ∧ T.y ≤ U.y ∧ U.y ≤ S.global U.y ∧ S.global U.y ≤ S.exact ∧
    U.r = S.global U.y - U.y ∧ 0 ≤ U.r ∧ EntryLE 0 U.R ∧
    U.E = 1-(1-S.jac U.y)*U.R ∧ EntryLE 0 U.E := by sorry

end HighPrecSAC1.Main
