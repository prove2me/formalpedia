-- Prove2me | Theorems.Thm_FourierRankQLB_lemma_A_1
-- name    : FourierRankQLB.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:53.723321+00:00
-- url     : https://prove2.me/theorems/f2736311-cd42-4444-8ca5-230930d4e59d
-- title:
--   Lemma A.1 — continuous membership has rank-one growth
-- statement:
--   Let $n\ge2$, let $(Y,\nu)$ be $\sigma$-finite, $K$ a separable Hilbert space, and $q:Y\to\mathbb R^n$, $\tau:Y\to\mathbb R$ measurable, with
--   $$
--   \phi(Q,y)=(-1)^{\mathbf 1[q(y)^TQq(y)\le\tau(y)]} .
--   $$
--   Then the multiplication operator $(M\Psi)(Q,y)=\phi(Q,y)\Psi(Q,y)$ satisfies, for every $r\ge0$,
--   $$
--   MW_r(Y,K)\subseteq W_{r+1}(Y,K).
--   $$
--
--   It extends the rank-one growth of Lemma 4.3 to an uncountable query register.
--
--   Differences from the source:
--
--   - encoding: the operator $M$ on $W_r(Y,K)$ → for each $\Psi\in W_r$, a class $\Phi\in W_{r+1}$ almost everywhere equal to $\phi\Psi$; reason: $M\Psi$ is that class
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Lemma A.1, p.49, with the standing assumptions of pp.48–49

import Mathlib
import Definitions.Def_FourierRankQLB_Wr
import Definitions.Def_FourierRankQLB_phase

open MeasureTheory

namespace FourierRankQLB

/-- Lemma A.1 (Continuous membership has rank-one growth). The multiplication operator
`(MΨ)(Q, y) = ϕ(Q, y) Ψ(Q, y)`, with `ϕ(Q, y) = (-1)^{1[q(y)ᵀQq(y) ≤ τ(y)]}` as in (95), maps
`W_r(Y, K)` into `W_{r+1}(Y, K)` for every `r`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Lemma A.1, p. 49, under the standing assumptions of Appendix A, pp. 48–49.

**Formalization Note.** The standing assumptions are `n ≥ 2`, `(Y, ν)` σ-finite, `K` separable and
`q`, `τ` measurable. The image of `Ψ` is the class `Φ` of the function `ϕ Ψ`. -/
theorem lemma_A_1 {n : ℕ} (hn : 2 ≤ n) {Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    [SigmaFinite ν] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] {q : Y → Fin n → ℝ} {τ : Y → ℝ} (hq : Measurable q)
    (hτ : Measurable τ) (r : ℕ) (Ψ : Lp K 2 ((haarO n).prod ν)) (hΨ : Ψ ∈ Wr n r ν K) :
    ∃ Φ ∈ Wr n (r + 1) ν K,
      Φ =ᵐ[(haarO n).prod ν] fun p => phase (q p.2) (τ p.2) p.1 • Ψ p := by sorry

end FourierRankQLB
