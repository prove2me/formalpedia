-- Prove2me | Theorems.Thm_NarrowDNF_Approx_theorem_1_2
-- name    : NarrowDNF.Approx.theorem_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:27.746261+00:00
-- url     : https://prove2.me/theorems/e9e824ba-412c-4546-97cc-2ac2cabd5942
-- title:
--   Theorem 1.2 — Narrow-DNF approximation
-- statement:
--   There is an absolute real constant $C>0$ such that, for every integer $n\ge1$, every $K>0$, every $0<p\le1/2$, every $0<\varepsilon<1$, and every coordinatewise increasing Boolean function $f:\{0,1\}^n\to\{0,1\}$ satisfying $I_p(f)\le K$, there is a finite monotone DNF $g$ such that
--   $$\operatorname{width}(g)\le\exp\!\left(\frac{C(K+1)^2}{\varepsilon^2}\right),\qquad
--   \mathbb P_p[f(X)\ne g(X)]\le\varepsilon.$$
--   The constant is chosen before the dimension, influence bound, bias, tolerance and function. Influence is independent-coordinate resampling influence, and disagreement is the two-sided error under the actual product law. There is no mean, symmetry, Fourier-degree or term-count restriction. Both constant functions have width-zero witnesses.
--
--   This is the dimension- and low-bias-uniform approximation result; it asserts existence without an efficient-construction claim.
--
--   Differences from the source:
--   - encoding: coordinates [n] and bits {0,1} → Fin n and Bool with pointwise false < true; reason: coordinate relabeling preserves all source instances
--   - encoding: product probabilities and expectations → published Bernoulli event sums and exact real finite weighted sums; reason: the finite product law is identical and every cost is integrable
--   - encoding: a monotone DNF with bounded width → a finite set of positive coordinate terms, its actual evaluation, and a real bound on its natural syntactic width; reason: every finite source DNF has the same representation after deleting duplicate terms, and every such witness is a source DNF
-- source:
--   Chenghua Liu, Boning Meng, STOC 2027 submission #1509 (October 2026), Theorem 1.2, p. 2 (PDF p. 3); proof p. 9 (PDF p. 10)

import Definitions.Def_NarrowDNF_Approx_DNF

namespace NarrowDNF.Approx

theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ K : ℝ, 0 < K →
      ∀ p : ℝ, 0 < p → p ≤ 1 / 2 → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ f : Cube n → Bool, Monotone f → FriedgutCoalition.totalPInfl p f ≤ K →
      ∃ g : DNF n, (width g : ℝ) ≤ Real.exp (C * (K + 1) ^ 2 / ε ^ 2) ∧
        error p f (evalDNF g) ≤ ε := by sorry

end NarrowDNF.Approx
