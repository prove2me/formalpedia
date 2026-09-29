-- Prove2me | Theorems.Thm_HomeoLine_exists_zpow_apply_gt
-- name    : HomeoLine.exists_zpow_apply_gt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-10T15:46:05.190084+00:00
-- url     : https://prove2.me/theorems/5be2d128-a59a-482e-98ca-a5c71ca684f4
-- title:
--   An orientation-preserving homeomorphism of the line with no fixed point in $[c,d]$ carries $c$ beyond $d$
-- statement:
--   Let $f$ be an orientation-preserving homeomorphism of $\mathbb{R}$ — equivalently, a strictly increasing bijection $\mathbb{R}\to\mathbb{R}$, continuity being automatic — and let $c,d$ be real numbers. Suppose $f$ has **no fixed point in the closed interval $[c,d]$**. Then some integer iterate of $f$ carries $c$ strictly beyond $d$:
--
--   $$\exists\, n \in \mathbb{Z}, \qquad f^{\,n}(c) > d.$$
--
--   The exponent may be negative — if $f$ moves $c$ downwards then only negative $n$ can work — and it may be zero, which is what covers the degenerate case $c > d$, where the interval is empty and the hypothesis says nothing. Nothing canonical is produced: there is no least such $n$ and no bound on $|n|$.
--
--   The point is that a bounded orbit would have to accumulate at a fixed point inside $[c,d]$. This is the one-generator case of the companion lemma `HomeoLine.exists_mem_closure_apply_gt`, from which it can be recovered by taking $g = f$; it is stated separately because the explicit $\exists n \in \mathbb{Z}$ form is what callers want.
--
--   **Formalization note.** No piecewise-linear or compact-support hypothesis is imposed, so this holds throughout $\mathrm{Homeo}_+(\mathbb{R})$.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Inventiones mathematicae 79 (1985), 485-498; Lemma (3.4) resp. (3.5) of Section 3. Note the paper's own remark that these two lemmas 'apply to arbitrary orientation-preserving homeomorphisms of R' -- they are stated here in that generality, with no piecewise-linear hypothesis.

import Mathlib

namespace HomeoLine

theorem exists_zpow_apply_gt (f : ℝ ≃o ℝ) {c d : ℝ} (h : ∀ t ∈ Set.Icc c d, f t ≠ t) :
    ∃ n : ℤ, d < (f ^ n) c := by
  sorry

end HomeoLine
