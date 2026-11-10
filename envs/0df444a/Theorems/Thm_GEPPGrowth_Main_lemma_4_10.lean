-- Prove2me | Theorems.Thm_GEPPGrowth_Main_lemma_4_10
-- name    : GEPPGrowth.Main.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:37:58.711181+00:00
-- url     : https://prove2.me/theorems/46b24731-3991-4299-87a9-63756cefea2a
-- title:
--   Lemma 4.10 — Wishart determinant law
-- statement:
--   Let $n\ge p$. For $X\sim W_p(I_p,n)$,
--
--   $$
--   \det(X)\overset{d}{=}\prod_{i=0}^{p-1}x_i
--   $$,
--
--   where $x_i\sim\chi^2_{n-i}$ are independent.
--
--   This is the determinant distribution used for real Gaussian Gram matrices.
--
--   Differences from the source:
--   - encoding: equality in distribution with independent chi-square factors → equality of determinant pushforward measure and the product-law pushforward; reason: records joint independence and degrees n-i exactly
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Lemma 4.10, printed p.9, PDF p.10

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Lemma 4.10, printed p.9 / PDF p.10. Product measure records joint independence, not only the individual chi-square marginals. -/
theorem lemma_4_10 (p n : ℕ) (hp : 0 < p) (hpn : p ≤ n) :
    (wishart (1 : Mat p) n).map Matrix.det =
      (Measure.pi (fun i : Fin p => chiSquare (n-i.val))).map (fun x => ∏ i, x i) := by sorry

end GEPPGrowth.Main
