-- Prove2me | Theorems.Thm_FuzzyExtractors_ImprovedJS_theorem_6_1
-- name    : FuzzyExtractors.ImprovedJS.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:11.346844+00:00
-- url     : https://prove2.me/theorems/ad3c94bd-3c2d-4f5d-bcd3-d84fa876fe18
-- title:
--   Theorem 6.1 — Construction 5 is an average-case $(\mathrm{SDif}_s(\mathcal U), m, m-t\log n, t)$ secure sketch
-- statement:
--   Let $\mathcal F$ be a finite field with $n$ elements, used as the universe $\mathcal U=\mathcal F$, and let $t\le s$ be natural numbers. Let $(\mathsf{SS},\mathsf{Rec})$ be the improved Juels–Sudan sketch (Construction 5): $\mathsf{SS}(w)$ outputs the coefficients of degree $s-1$ down to $s-t$ of $\prod_{x\in w}(z-x)$, and $\mathsf{Rec}$ decodes by Reed–Solomon decoding and root finding. Then for every real $m$, $(\mathsf{SS},\mathsf{Rec})$ is an average-case
--
--   $$\big(\mathrm{SDif}_s(\mathcal U),\ m,\ m-t\log_2 n,\ t\big)\text{-secure sketch}.$$
--
--   That is:
--   1. (correctness) for all $s$-element sets $w,w'\subseteq\mathcal F$ with $|w\triangle w'|\le t$, $\mathsf{Rec}(w',\mathsf{SS}(w))=w$;
--   2. (security) for all random variables $W$ over $s$-element subsets of $\mathcal F$ and $I$ (arbitrary auxiliary information) with $\tilde H_\infty(W\mid I)\ge m$, one has $\tilde H_\infty\big(W\mid(\mathsf{SS}(W),I)\big)\ge m-t\log_2 n$.
--
--   In particular the entropy loss of the scheme is at most $t\log n$, which §6.2 shows to be essentially optimal for $n\gg s$.
--
--   **Formalization Note.** The paper leaves $t\le s$ implicit; it is a hypothesis here. "$n$ is a prime power" is automatic since $\mathcal U$ is a finite field. The storage bound ("storage at most $t\log n$") holds by construction, since the sketch is a vector in $\mathcal F^t$, and is not restated. The running-time clause ("SS() and Rec() run in time polynomial in $s$, $t$ and $\log n$") is dropped: there is no complexity substrate. Logarithms are base 2, $\tilde H_\infty$ is in the joint form (see the definition module), and the auxiliary variable $I$ ranges over an arbitrary type.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Theorem 6.1, p. 22

import Mathlib
import Definitions.Def_FuzzyExtractors_ImprovedJS_Basic

namespace FuzzyExtractors.ImprovedJS

/-- Theorem 6.1 (Analysis of Improved JS), p. 22: over a finite field 𝔽 with n elements and for
t ≤ s, Construction 5 is an average-case (SDif_s(𝔽), m, m − t log n, t)-secure sketch, for every m. -/
theorem theorem_6_1 {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (s t : ℕ) (hts : t ≤ s)
    (m : ℝ) :
    FuzzyExtractors.Hamming.IsAvgSecureSketch (sdifDist (𝓤 := 𝔽) (s := s)) m
      (m - t * Real.logb 2 (Fintype.card 𝔽)) t (sketch s t) (recover s t) := by sorry

end FuzzyExtractors.ImprovedJS
