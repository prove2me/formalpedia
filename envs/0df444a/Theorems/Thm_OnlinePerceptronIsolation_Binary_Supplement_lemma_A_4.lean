-- Prove2me | Theorems.Thm_OnlinePerceptronIsolation_Binary_Supplement_lemma_A_4
-- name    : OnlinePerceptronIsolation.Binary.Supplement.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:12:38.720604+00:00
-- url     : https://prove2.me/theorems/8050b415-436e-4eb8-8ac9-3501cd32a473
-- title:
--   Lemma A.4 — uniqueness implies a thin shell for rectangles
-- statement:
--   Let $m,r\ge2$, let $\phi:\mathbb R^m\to\{-1,+1\}$ be measurable, and let $B\subseteq\mathbb R^m$ be any rectangle with arbitrary interval endpoints. Sample independent $Y_i\sim N(0,I_m)$ and set
--   $$S=\frac1{\sqrt r}\sum_{i=1}^r\phi(Y_i)Y_i,\qquad\delta=6\sqrt{\frac{\log m}{r}}.$$
--   For the full-cube uniqueness event of Definition 4.4 and inward shrink of Definition 4.3,
--   $$\mathbb P(U_{\phi,B})\le\mathbb P\{S\in B\setminus B^{-\delta}\}+\frac2m.$$
--   The constants are uniform over the dimensions, rectangle and sign map. They instantiate the source's existential $\Theta$ and $O$ bounds using its proof with $C=3$. This is the thin-shell input for Lemma 4.5.
--
--   Differences from the source:
--   - encoding: one-based sign cube and real coordinates → zero-based Fin indices and exact real-valued signs; reason: coordinate relabelling preserves all signings, scores and Hamming distances
--   - encoding: products of arbitrary real intervals → a Rectangle structure of order-connected coordinate sets with its product carrier; reason: every permitted endpoint convention, empty interval and unbounded interval is represented
--   - encoding: there exists delta = Theta(sqrt(log m / r)) and an O(1/m) error → delta = 6 sqrt(log m / r) and error 2/m; reason: Eqs. (A.29)–(A.31) reuse (A.23)–(A.25); C=3 gives delta=6 sqrt(log m/r) and 2 m^(1-9/2) < 2/m for m≥2
--   - encoding: finite endpoints move inward and infinite endpoints stay fixed; an empty rectangle stays empty → EReal infimum/supremum endpoints and a guarded closed-interval shrink; reason: extended endpoints retain unbounded intervals without introducing artificial real endpoints
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Lemma A.4, printed p. 21, PDF p. 23; constants from proof Eqs. (A.23)–(A.25), printed pp. 20–21, PDF pp. 22–23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_RectangleUniqueness
import Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_RectangleShrink
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary.Supplement

/-- Lemma A.4, printed p.21 / PDF p.23. Equations A.29--A.31 and A.23--A.25,
with C=3, give delta=6 sqrt(log(m)/r) and error at most 2/m. -/
theorem lemma_A_4 (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r)
    (ϕ : (Fin m → ℝ) → ℝ) (hϕ : Measurable ϕ)
    (hsign : ∀ y, ϕ y = 1 ∨ ϕ y = -1) (B : Rectangle m) :
    (ABPOnline.gaussMat m r).real (rectangleUniquenessEvent ϕ B) ≤
      (ABPOnline.gaussMat m r).real
        {Y | signingScore Y (fun i => ϕ (fun j => Y (j, i))) ∈
          B.carrier \ B.shrink (6 * Real.sqrt (Real.log m / r))} +
      2 / m := by sorry

end OnlinePerceptronIsolation.Binary.Supplement
