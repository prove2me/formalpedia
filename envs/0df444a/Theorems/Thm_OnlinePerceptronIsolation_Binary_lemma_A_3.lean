-- Prove2me | Theorems.Thm_OnlinePerceptronIsolation_Binary_lemma_A_3
-- name    : OnlinePerceptronIsolation.Binary.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:16.883932+00:00
-- url     : https://prove2.me/theorems/d0a1b1e3-0a4c-45fd-a980-9c155911ca89
-- title:
--   Lemma A.3 — uniqueness implies a thin shell
-- statement:
--   Let $m,r\ge2$, let $\phi:\mathbb R^m\to\{-1,+1\}$ be measurable, and let $\theta\in\mathbb R^m$. For independent standard Gaussian columns $Y_1,\ldots,Y_r$, write $S=r^{-1/2}\sum_i\phi(Y_i)Y_i$ and $O_u=\{x:x_j\ge u_j\text{ for all }j\}$. With
--   $$\delta=6\sqrt{\frac{\log m}{r}},$$
--   one has
--   $$\mathbb P(U_{\phi,\theta})\le \mathbb P(S\in O_\theta\setminus O_{\theta+\delta\mathbf1_m})+\frac2m.$$
--   The explicit width has the source's $\Theta(\sqrt{\log m/r})$ size, and the error is uniform in $\phi$ and $\theta$. This is the orthant-shell statement used by the uniqueness bound.
--
--   Differences from the source:
--   - encoding: one-based sign cube and coordinates → zero-based Fin indices and exact real-valued signs; reason: a bijection of coordinate labels preserves every signing and Hamming distance
--   - encoding: delta is Theta of sqrt(log(m)/r) and the error is O(1/m) → delta equals 6 sqrt(log(m)/r) and error is at most 2/m; reason: equations (A.19)-(A.25) give these choices by setting the proof parameter C to 3
--   - encoding: closed upper orthants → Set.Ici in the coordinatewise order; reason: these sets are exactly the source orthants
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Lemma A.3, Eqs. (A.11)-(A.12), printed p.20, PDF p.22; Eqs. (A.19)-(A.25), printed pp.20-21, PDF pp.22-23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Uniqueness
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- Lemma A.3, printed p.20 / PDF p.22. Equations A.19--A.25 with C=3 give
δ=6 sqrt(log(m)/r) and error at most 2/m, uniformly over the sign map and threshold. -/
theorem lemma_A_3 (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r)
    (ϕ : (Fin m → ℝ) → ℝ) (hϕ : Measurable ϕ)
    (hsign : ∀ y, ϕ y = 1 ∨ ϕ y = -1) (θ : Fin m → ℝ) :
    (ABPOnline.gaussMat m r).real (uniquenessEvent ϕ θ) ≤
      (ABPOnline.gaussMat m r).real
        {Y | signingScore Y (fun i => ϕ (fun j => Y (j, i))) ∈
          Set.Ici θ \ Set.Ici (fun j => θ j + 6 * Real.sqrt (Real.log m / r))} +
      2 / m := by sorry

end OnlinePerceptronIsolation.Binary
