-- Prove2me | Theorems.Thm_HalfIndMatch_Supplement_theorem_2_7
-- name    : HalfIndMatch.Supplement.theorem_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:04:32.893657+00:00
-- url     : https://prove2.me/theorems/ae732f4d-dfde-4125-a77d-4bd4181fedcd
-- title:
--   Theorem 2.7 — no random degree-$D$ polynomial is a $((\frac12+\varepsilon)\Phi,\delta,\gamma,\eta)$-optimizer in $G(n,d/n)$
-- statement:
--   Let $\Phi=(n\log d)/d$ and $m=\binom n2$. For every $\varepsilon>0$ and every sufficiently large fixed $d$, there are constants $c_1=c_1(\varepsilon,d)>0$ and $c_2=c_2(\varepsilon,d)>0$ such that the following holds for all sufficiently large $n$. Let $D=D_n\in\mathbb N$, $\gamma=\gamma_n\ge1$, $\delta=\delta_n\in[0,1]$ and $\eta=\eta_n>0$ satisfy
--
--   $$D\le\frac{c_1n}{\gamma\log n},\qquad\delta\le\exp(-c_2\gamma D\log n),\qquad\eta\le\frac{\varepsilon\Phi}{64m},$$
--
--   and let $k=(\tfrac12+\varepsilon)\Phi$. Then there is no random polynomial of degree at most $D$ that is a $(k,\delta,\gamma,\eta)$-optimizer for the induced matching problem in $G(n,d/n)$ (Definition 2.5).
--
--   This is the low-degree barrier matching Theorem 2.6: polynomials of degree up to order $n/\log n$, even with independent internal randomness, cannot exceed $\Phi/2$ by a constant factor at the stated success probabilities.
--
--   **Formalization Note** "Every sufficiently large fixed $d$" is $\exists d_0\ \forall d\ge d_0$ over real $d$; $c_1,c_2$ and the threshold on $n$ depend only on $(\varepsilon,d)$, never on $D,\gamma,\delta,\eta$. A random polynomial is an arbitrary probability space $(\Omega,\mu)$ of seeds and $f:\Omega\to(\mathcal E_n\to\mathbb R[G_e:e\in\mathcal E_n])$ of degree at most $D$ for every seed, with $\xi\mapsto f_e(G;\xi)$ measurable for every graph $G$ and edge $e$ (what makes the joint expectation and probability defined). $\log$ is natural.
--
--   Differences from the source:
--   - reading: $D\in\mathbb N$ → $1\le D$; reason: with $D=0$ the hypotheses allow $\delta=1$, which every polynomial meets (e.g. $f\equiv0$), so the literal $D=0$ case is false; the paper's convention is $1\le D$ (Theorem 1.2, p.4) and its proof uses $\gamma D\ge1$.
--   - encoding: a random seed $\xi$ sampled independently of $G$ → an arbitrary probability space $(\Omega,\mu)$ in `Type` with $\xi\mapsto f_e(G;\xi)$ measurable for all $G,e$; reason: the measurability is what gives the paper's expectation and probability a meaning, and it excludes no polynomial for which they are defined.
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), Theorem 2.7, p.12 (PDF p.14); D ≥ 1 convention: Theorem 1.2, p.4 (PDF p.6); proof in §5, pp.22–32 (PDF pp.24–34)

import Mathlib
import Definitions.Def_HalfIndMatch_Supplement_roundM
import Definitions.Def_HalfIndMatch_Supplement_IsOptimizer

open scoped Classical
open MeasureTheory

namespace HalfIndMatch.Supplement

/-- **Theorem 2.7** (low-degree barrier). For every `ε > 0` and every sufficiently large fixed `d`,
there are constants `c₁ = c₁(ε, d) > 0` and `c₂ = c₂(ε, d) > 0` such that for all sufficiently large
`n`: if `D ∈ ℕ`, `γ ≥ 1`, `δ ∈ [0, 1]`, `η > 0` satisfy
`D ≤ c₁ n/(γ log n)`, `δ ≤ exp(−c₂ γ D log n)` and `η ≤ εΦ/(64 m)`, and `k = (1/2 + ε)Φ`, then no
random polynomial of degree at most `D` is a `(k, δ, γ, η)`-optimizer for the induced matching
problem in `G(n, d/n)`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs:
Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…),
Theorem 2.7, p.12 (PDF p.14).

**Formalization Note** `D ∈ ℕ` is read as `D ≥ 1`, the paper's convention (Theorem 1.2, p.4:
"for 1 ≤ D ≤ cn/log n"); with `D = 0` the hypotheses allow `δ = 1`, which every polynomial meets.
A random polynomial is an arbitrary probability space `(Ω, μ)` of seeds and a map
`f : Ω → (𝓔ₙ → MvPolynomial 𝓔ₙ ℝ)` of degree `≤ D` for every seed, with `ξ ↦ f_{ξ,e}(G)` measurable
for every graph `G` and edge `e` (the measurability that makes the expectation and probability
meaningful). `c₁, c₂` and the threshold `N` depend on `(ε, d)` only. `log` is natural. -/
theorem theorem_2_7 (ε : ℝ) (hε : 0 < ε) :
    ∃ d₀ : ℝ, ∀ d : ℝ, d₀ ≤ d →
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ (D : ℕ) (γ δ η : ℝ), 1 ≤ D → 1 ≤ γ → 0 ≤ δ → δ ≤ 1 → 0 < η →
          (D : ℝ) ≤ c₁ * n / (γ * Real.log n) →
          δ ≤ Real.exp (-(c₂ * γ * D * Real.log n)) →
          η ≤ ε * Phi n d / (64 * mEdges n) →
          ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (f : Ω → Edges n → MvPolynomial (Edges n) ℝ),
            (∀ ξ e, (f ξ e).totalDegree ≤ D) →
            (∀ (G : SimpleGraph (Fin n)) (e : Edges n),
              Measurable fun ξ => MvPolynomial.eval (edgeInd G) (f ξ e)) →
            ¬ IsOptimizer n d ((1 / 2 + ε) * Phi n d) δ γ η Ω μ f := by sorry

end HalfIndMatch.Supplement
