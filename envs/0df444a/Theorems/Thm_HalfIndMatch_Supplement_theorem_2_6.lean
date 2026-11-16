-- Prove2me | Theorems.Thm_HalfIndMatch_Supplement_theorem_2_6
-- name    : HalfIndMatch.Supplement.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:03:55.716962+00:00
-- url     : https://prove2.me/theorems/51634425-05da-41d2-a7dd-cd133b438d06
-- title:
--   Theorem 2.6 — a constant-degree polynomial is a $((\frac12-\varepsilon)\Phi,e^{-cn^{1/3}},\gamma,\frac{\varepsilon\Phi}{128m})$-optimizer in $G(n,d/n)$
-- statement:
--   Let $\Phi=(n\log d)/d$ and $m=\binom n2$. For every $0<\varepsilon<\tfrac12$ and every sufficiently large fixed $d$, there exist an integer $D=D(d,\varepsilon)\ge1$ and constants $\gamma=\gamma(d,\varepsilon)\ge1$ and $c=c(d,\varepsilon)>0$ such that, for all sufficiently large $n$, there is a deterministic polynomial $f$ of degree at most $D$ that is a
--
--   $$\Big(\big(\tfrac12-\varepsilon\big)\Phi,\ \exp(-cn^{1/3}),\ \gamma,\ \frac{\varepsilon\Phi}{128m}\Big)\text{-optimizer}$$
--
--   for the induced matching problem in $G(n,d/n)$ (Definition 2.5). In particular, the rounding $\mathcal M^{\eta}_f(G)$, $\eta=\varepsilon\Phi/(128m)$, is an induced matching of $G$ with at least $(\tfrac12-\varepsilon)\Phi$ edges with probability at least $1-\exp(-cn^{1/3})$.
--
--   Since the largest induced matching of $G(n,d/n)$ has about $\Phi$ edges, constant-degree polynomials reach half of the optimum; together with Theorem 2.7 this makes $\Phi/2$ the sharp threshold for low-degree algorithms.
--
--   **Formalization Note** "Every sufficiently large fixed $d$" is $\exists d_0\ \forall d\ge d_0$ over real $d$. The integer $D$ and the constants $\gamma,c$ depend only on $(d,\varepsilon)$, the threshold on $n$ likewise; the polynomial may depend on $n$. $n^{1/3}$ is the real power and $\log$ is natural. A polynomial is `Edges n → MvPolynomial (Edges n) ℝ` with every `totalDegree ≤ D`. The "in particular" clause appears as the extra conjunct that the rounding is an induced matching of every graph (the published `HalfIndMatch.IsInducedMatching`); its probability part is the second condition of the optimizer.
--
--   Differences from the source: none.
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), Theorem 2.6 and eq. (2), p.11 (PDF p.13); proof in §4, pp.16–22 (PDF pp.18–24)

import Mathlib
import Definitions.Def_HalfIndMatch_IsInducedMatching
import Definitions.Def_HalfIndMatch_Supplement_roundM
import Definitions.Def_HalfIndMatch_Supplement_IsOptimizer

open scoped Classical

namespace HalfIndMatch.Supplement

/-- **Theorem 2.6** (low-degree achievability). For every `0 < ε < 1/2` and every sufficiently large
fixed `d`, there are an integer `D = D(d, ε) ≥ 1` and constants `γ = γ(d, ε) ≥ 1`, `c = c(d, ε) > 0`
such that, for all sufficiently large `n`, some deterministic polynomial of degree at most `D` is a
`((1/2 − ε)Φ, exp(−c n^{1/3}), γ, εΦ/(128 m))`-optimizer for the induced matching problem in
`G(n, d/n)`. In particular, its rounding is an induced matching, with at least `(1/2 − ε)Φ` edges
with probability `≥ 1 − exp(−c n^{1/3})`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs:
Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…),
Theorem 2.6 and eq. (2), p.11 (PDF p.13).

**Formalization Note** "Every sufficiently large fixed `d`" is `∃ d₀, ∀ real d ≥ d₀`; `D, γ, c` depend
on `(d, ε)` only and the threshold `N` on `(d, ε)`; the polynomial may depend on `n`. `Φ = n log d/d`,
`m = C(n, 2)`, `n^{1/3}` is the real power. The "in particular" clause is stated as the extra
conjunct that `M^η_f(G)` is an induced matching of `G` for every `G` (its probability part is the
second clause of the optimizer property). -/
theorem theorem_2_6 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ d₀ : ℝ, ∀ d : ℝ, d₀ ≤ d →
      ∃ D : ℕ, 1 ≤ D ∧ ∃ γ : ℝ, 1 ≤ γ ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ f : Edges n → MvPolynomial (Edges n) ℝ,
          (∀ e, (f e).totalDegree ≤ D) ∧
          IsDetOptimizer n d ((1 / 2 - ε) * Phi n d) (Real.exp (-(c * (n : ℝ) ^ ((1 : ℝ) / 3)))) γ
            (ε * Phi n d / (128 * mEdges n)) f ∧
          ∀ G : SimpleGraph (Fin n),
            IsInducedMatching G (roundM (ε * Phi n d / (128 * mEdges n)) f G) := by sorry

end HalfIndMatch.Supplement
