-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_minor_arc_bilinear_fourth
-- name    : OAI.TwoPointCorrelations.minor_arc_bilinear_fourth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:01.468993+00:00
-- url     : https://prove2.me/theorems/63935905-1b02-4236-8ffd-32d18d736c76
-- title:
--   A fourth-moment Cauchy–Schwarz bound for the minor-arc bilinear window
-- statement:
--   Let $P$ be a finite set of positive naturals with $q\le2p$ for all $p,q\in P$; let $X,M,H$ be naturals and $d\ge1$; let $a,c:\mathbb N\to\mathbb C$ with $|a(m)|\le1$ for $m<M$ and $|c(p)|\le1$ on $P$; and let $\alpha,V$ be reals with $H/(dp)+1\le V$ for every $p\in P$ (natural-number product $dp$, real division). Then
--
--   $$\Big(\sum_{k<X}\big|\mathcal W(k)\big|\Big)^4\le M^3\,X(3H+1)^3\sum_{p_1,p_2,p_3,p_4\in P}g\big(V,\alpha(p_1+p_2-p_3-p_4)\big),$$
--
--   where $\mathcal W(k)$ = `minorArcBilinearWindow P M H d a c α k` $=\sum_{m<M}a(m)\sum_{p\in P}$ `minorArcWindowTerm M (dp) k H (c p) (αp) m` and $g(V,\beta)$ = `minorArcGeometricBound V β` is $V$ if $e(\beta)=1$ and $\min(V,2/|e(\beta)-1|)$ otherwise, $e(\beta)=e^{2\pi i\beta}$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.minor_arc_bilinear_fourth`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset

theorem minor_arc_bilinear_fourth (P : Finset ℕ) (X M H d : ℕ) (hd : 0 < d)
    (hP : ∀ p ∈ P, 0 < p ∧ ∀ q ∈ P, q ≤ 2 * p)
    (a c : ℕ → ℂ) (ha : ∀ m ∈ range M, ‖a m‖ ≤ 1) (hc : ∀ p ∈ P, ‖c p‖ ≤ 1)
    (α V : ℝ) (hV : ∀ p ∈ P, (H : ℝ) / (d * p : ℕ) + 1 ≤ V) :
    (∑ k ∈ range X, ‖minorArcBilinearWindow P M H d a c α k‖) ^ 4 ≤
      (M : ℝ) ^ 3 * (X * (3 * H + 1) ^ 3 : ℕ) *
        ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
          minorArcGeometricBound V (α * ((p₁ : ℝ) + p₂ - p₃ - p₄)) := by
  sorry

end OAI.TwoPointCorrelations
