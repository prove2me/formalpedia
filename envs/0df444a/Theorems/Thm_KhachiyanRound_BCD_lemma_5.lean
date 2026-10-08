-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_lemma_5
-- name    : KhachiyanRound.BCD.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:19.141973+00:00
-- url     : https://prove2.me/theorems/15d586c2-e460-48c0-97cf-46f69a3428f5
-- title:
--   Lemma 5, p. 315 — the slice E of √(1 + (1 + ε)n) E′_p at y = 1 satisfies ν⁻²E ⊆ conv.hull(𝒜) ⊆ E, ν = √((1 + ε)n)
-- statement:
--   Let $n \ge 1$ and let $a_1,\dots,a_m \in \mathbb{R}^n$ have affine hull $\mathbb{R}^n$ (3.1). Let $\varepsilon \ge 0$, let $q$ be a point of the unit simplex in $\mathbb{R}^m$ whose block matrix
--   $$M(q) = \begin{pmatrix} \sum_j q_j a_j a_j^{\mathsf T} & \sum_j q_j a_j \\ \sum_j q_j a_j^{\mathsf T} & 1\end{pmatrix}$$
--   is positive definite, and let $E'_q = \{z \in \mathbb{R}^{n+1} \mid z^{\mathsf T}M(q)^{-1}z \le 1\}$ as in (3.4). Assume both inclusions of (3.5), with $\mathcal A' = \{\pm(a_j;1)\}$:
--   $$E'_q \subseteq \operatorname{conv}(\mathcal A') \subseteq \sqrt{1 + (1+\varepsilon)n}\;E'_q.$$
--   Let $E = \{x \in \mathbb{R}^n \mid (x;1) \in \sqrt{1+(1+\varepsilon)n}\,E'_q\}$ (the intersection with the hyperplane $y = 1$), whose centre is $b = \sum_j q_j a_j$, and let $\nu = \sqrt{(1+\varepsilon)n}$. Then
--   $$\nu^{-2}E \subseteq \operatorname{conv}(\mathcal A) \subseteq E,$$
--   where $\nu^{-2}E$ is the image of $E$ under the homothety of ratio $\nu^{-2}$ about $b$.
--
--   Lemma 5 turns a rounding of the lifted symmetric set into a $(1+\varepsilon)n$-rounding of the original, not necessarily symmetric, set.
--
--   **Formalization Note** The hypotheses include both inclusions of (3.5), as in the page's setting. The shrinking $\nu^{-2}E$ is about the centre $b$ of $E$, as in the page's reduction to $b = 0$ (3.7); a scaling about the origin would be a different, generally false, statement.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 315, Lemma 5, (3.4)–(3.6)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem lemma_5 {m n : ℕ} (a : Fin m → Fin n → ℝ) (hn : 1 ≤ n)
    (hfull : affineSpan ℝ (Set.range a) = ⊤) (ε : ℝ) (hε : 0 ≤ ε)
    (q : Fin m → ℝ) (hq : q ∈ stdSimplex ℝ (Fin m)) (hpd : (blockMatrix a q).PosDef)
    (hinner : Eprime a q ⊆ convexHull ℝ (Set.range (liftPts a)))
    (hround : convexHull ℝ (Set.range (liftPts a)) ⊆
      Real.sqrt (1 + (1 + ε) * n) • Eprime a q) :
    (AffineMap.homothety (∑ j, q j • a j) ((1 + ε) * (n : ℝ))⁻¹) '' lemma5Ellipsoid a q ε ⊆
        convexHull ℝ (Set.range a) ∧
      convexHull ℝ (Set.range a) ⊆ lemma5Ellipsoid a q ε := by sorry
end KhachiyanRound.BCD
