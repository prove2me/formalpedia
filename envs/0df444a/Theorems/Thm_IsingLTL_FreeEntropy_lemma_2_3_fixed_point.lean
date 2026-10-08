-- Prove2me | Theorems.Thm_IsingLTL_FreeEntropy_lemma_2_3_fixed_point
-- name    : IsingLTL.FreeEntropy.lemma_2_3_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:34.794985+00:00
-- url     : https://prove2.me/theorems/7885d4dd-425a-4b8b-8da0-d5a957164e72
-- title:
--   Lemma 2.3 — the recursion (2.6) converges monotonically to its unique fixed point on $[0,\infty)$
-- statement:
--   Let $P$ be a degree distribution with size-biased law $\rho$, $\beta\ge0$, and let $h^{(0)}=0$ and, for $t\ge0$,
--   $$h^{(t+1)}\overset{d}{=}B+\sum_{i=1}^{K-1}\xi(\beta,h^{(t)}_i),\qquad \xi(\beta,h)=\operatorname{atanh}[\tanh(\beta)\tanh(h)],$$
--   where $K\sim\rho$ and the $h^{(t)}_i$ are i.i.d. copies of $h^{(t)}$ independent of $K$. If $B>0$ and $\rho$ has finite first moment, then:
--
--   1. the laws of $h^{(t)}$ are stochastically monotone: $\mathbb P(h^{(t)}>a)\le\mathbb P(h^{(t+1)}>a)$ for every $t$ and $a$;
--   2. the recursion (2.6) has exactly one fixed point $h^*$ supported on $[0,\infty)$;
--   3. $h^{(t)}$ converges in distribution to $h^*$.
--
--   The law of $h^*$ is the "cavity field" distribution entering the Bethe formula (2.9).
--
--   **Formalization Note** $\beta\ge0$ is the paper's standing assumption (p. 1). Convergence in distribution is weak convergence of probability measures on $\mathbb R$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 5, Lemma 2.3, (2.6)-(2.7)

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_DistRecursion

namespace IsingLTL.FreeEntropy

open MeasureTheory Filter Topology

/-- **Lemma 2.3** (Dembo–Montanari, *Ising Models on Locally Tree-Like Graphs*, arXiv:0804.4726v3,
p. 5). Let `h^{(0)} = 0` and `h^{(t+1)} =ᵈ B + ∑_{i=1}^{K−1} ξ(β, h^{(t)}_i)` (2.6), with `K ∼ ρ`,
`ξ(β, h) = atanh[tanh β tanh h]` (2.7), and the `h^{(t)}_i` i.i.d. copies of `h^{(t)}` independent of
`K`. If `B > 0` and `ρ` has finite first moment, then the distributions of `h^{(t)}` are
stochastically monotone and `h^{(t)}` converges in distribution to the unique fixed point `h*` of
(2.6) that is supported on `[0, ∞)`.

Formalization Note: `ρ` is the size-biased law of a degree distribution `P` (2.1). The hypothesis
`β ≥ 0` is the paper's standing assumption (ferromagnetic model, p. 1), used by the proof through
Griffiths' inequality. "Stochastically monotone" is first-order stochastic order of consecutive
laws, `Q_t((a, ∞)) ≤ Q_{t+1}((a, ∞))` for every `a` (`h^{(t)} ⪯ h^{(t+1)}`). Convergence in
distribution is convergence in `ProbabilityMeasure ℝ` (weak convergence). The conclusion asserts
existence and uniqueness of a fixed point supported on `[0, ∞)` and the convergence to it. -/
theorem lemma_2_3_fixed_point (D : DegreeDist) (hρ : D.RhoFiniteMean) (β B : ℝ) (hβ : 0 ≤ β)
    (hB : 0 < B) :
    (∀ (t : ℕ) (a : ℝ),
        (recLaw β B D t : Measure ℝ) (Set.Ioi a) ≤ (recLaw β B D (t + 1) : Measure ℝ) (Set.Ioi a)) ∧
      ∃ Q : ProbabilityMeasure ℝ, IsNonnegFixedPoint β B D Q ∧
        (∀ Q' : ProbabilityMeasure ℝ, IsNonnegFixedPoint β B D Q' → Q' = Q) ∧
        Tendsto (recLaw β B D) atTop (𝓝 Q) := by sorry

end IsingLTL.FreeEntropy
