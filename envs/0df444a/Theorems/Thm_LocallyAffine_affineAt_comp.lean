-- Prove2me | Theorems.Thm_LocallyAffine_affineAt_comp
-- name    : LocallyAffine.affineAt_comp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-14T11:44:32.06166+00:00
-- url     : https://prove2.me/theorems/4f70ab81-1acc-4ee0-95c8-0c431477d892
-- title:
--   Local affineness composes: affine near a point, composed with affine near its image, is affine near that point
-- statement:
--   Let $f, g \colon \mathbb{R} \to \mathbb{R}$ and let $x \in \mathbb{R}$. Suppose $f$ agrees with
--   an affine map on a neighbourhood of $x$, and $g$ agrees with an affine map on a neighbourhood of
--   $f(x)$:
--
--   $$f(y) = ay + b \quad \text{for } |y - x| < \varepsilon, \qquad\qquad g(y) = cy + d \quad
--   \text{for } |y - f(x)| < \delta .$$
--
--   Then the composite agrees with an affine map on a neighbourhood of $x$: there are $\eta > 0$
--   and reals $e, k$ with
--
--   $$g\bigl(f(y)\bigr) = e\,y + k \qquad \text{for } |y - x| < \eta .$$
--
--   Only existence is claimed. The statement does not tie $\eta$ to $\varepsilon$ and $\delta$, does
--   not name the composite's slope, and asserts no uniqueness. Note also that the second hypothesis
--   is anchored at the single point $f(x)$: it is not assumed that $f$ carries a neighbourhood of $x$
--   into the interval on which $g$ is affine — that is part of what the proof has to establish.
--
--   **Role.** Piecewise linearity is local affineness away from a small exceptional set, so this is
--   the step that makes such a class closed under composition. It is equally what lets one strip a
--   factor off a piecewise-linear map and still know the quotient is piecewise linear away from that
--   factor's breakpoints.
--
--   **No continuity is hypothesised, and none is needed.** An affine map carries its own modulus:
--   if $f$ has slope $a$ near $x$ then $|f(y) - f(x)| = |a|\,|y - x|$ exactly, so it suffices to
--   shrink the neighbourhood by a factor of $|a| + 1$ — which is why the hypothesis anchored at the
--   single point $f(x)$ is enough. The $+1$ merely avoids a division by zero: the slope $a = 0$ is
--   permitted, and then $f$ is constant near $x$.
--
--   **Formalization note.** Both hypotheses and the conclusion are stated as explicit existentials
--   over a symmetric open interval rather than through a named "locally affine" predicate, so the
--   statement stands alone against Mathlib with no definition of its own to import.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, pp. 487-488, where PLF(R) -- the piecewise linear homeomorphisms of the line with a finite breakpoint set, defined by affineness on a neighbourhood of every point off that set -- is introduced and used throughout as a group. PROVENANCE: this is NOT a numbered result of that paper, which treats closure of PLF(R) under composition as routine and does not prove it. The statement here is the elementary analysis step underneath that closure, and is more general than anything in the source: it is about arbitrary functions on the reals, with no piecewise linearity, no monotonicity, no finiteness and no continuity hypothesis anywhere.

import Mathlib

namespace LocallyAffine

theorem affineAt_comp {f g : ℝ → ℝ} {x : ℝ}
    (hf : ∃ ε > 0, ∃ a b : ℝ, ∀ y ∈ Set.Ioo (x - ε) (x + ε), f y = a * y + b)
    (hg : ∃ δ > 0, ∃ c d : ℝ, ∀ y ∈ Set.Ioo (f x - δ) (f x + δ), g y = c * y + d) :
    ∃ η > 0, ∃ e k : ℝ, ∀ y ∈ Set.Ioo (x - η) (x + η), g (f y) = e * y + k := by
  sorry

end LocallyAffine
