-- Prove2me | Theorems.Thm_NonconcaveUtil_Viscosity_lemma_ec_3_3
-- name    : NonconcaveUtil.Viscosity.lemma_ec_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:20.473551+00:00
-- url     : https://prove2.me/theorems/71b379bb-1fa1-47de-9930-6e54e5681379
-- title:
--   Lemma EC.3.3 — power majorant of a concave nondecreasing function
-- statement:
--   Let $f$ be concave and nondecreasing on $(B,\infty)$, with $B\ge0$, and suppose $f(w)/w^p\to0$ as $w\to\infty$ for $0<p<1$. Given $w_0>B$ and $\varepsilon>0$, there is a power majorant $f_1(w)=C_1w^q+C_2$ such that
--
--   $$p\le q<1,\qquad f(w)\le f_1(w)\ (w>B),\qquad f_1(w_0)\le f(w_0)+\varepsilon.$$
--
--   The lemma supplies a growth-class approximation for the concave envelope used in the unbounded-portfolio case.
--
--   **Formalization Note** Monotonicity is an explicit correction to the printed lemma, which is false for $f(w)=-\sqrt w$ on $w>0$. The application in this paper has a nondecreasing utility, and the proof invokes a positive-slope tangent. The majorant is required on the domain $w>B$ where $f$ is defined.
-- source:
--   Dai, Kou, Qian & Wan, Nonconcave utility maximization with portfolio bounds, accepted manuscript (Management Science 68(11), 2022; DOI 10.1287/mnsc.2021.4228), p. ec26 (PDF 58), Lemma EC.3.3; monotonicity correction disclosed

import Mathlib

open Filter Topology

namespace NonconcaveUtil.Viscosity

/-- Lemma EC.3.3, p. ec26, with the monotonicity used by its application and
the printed positive-slope argument. Without monotonicity the printed lemma
is false (for example `f(w) = -√w` on `w > 0`). -/
theorem lemma_ec_3_3 (B : ℝ) (hB : 0 ≤ B) (f : ℝ → ℝ)
    (hconc : ConcaveOn ℝ (Set.Ioi B) f)
    (hmono : MonotoneOn f (Set.Ioi B))
    (p : ℝ) (hp : 0 < p ∧ p < 1)
    (hsmall : Tendsto (fun w : ℝ => f w / w ^ p) atTop (𝓝 0))
    (w₀ ε : ℝ) (hw₀ : B < w₀) (hε : 0 < ε) :
    ∃ C₁ C₂ q : ℝ, p ≤ q ∧ q < 1 ∧
      (∀ w > B, f w ≤ C₁ * w ^ q + C₂) ∧
      C₁ * w₀ ^ q + C₂ ≤ f w₀ + ε := by sorry

end NonconcaveUtil.Viscosity
