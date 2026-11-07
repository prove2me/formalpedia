-- Prove2me | Theorems.Thm_LIPAlgorithm_lemma_4_4
-- name    : LIPAlgorithm.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:21.48321+00:00
-- url     : https://prove2.me/theorems/422547aa-cf6a-4db9-8222-fc16079da840
-- title:
--   Lemma 4.4 — local heat lower bound
-- statement:
--   There is an absolute constant $c>0$ such that, for every $n\ge1$, every rank-$n$ well-rounded lattice $L$ with $\lambda=\lambda_1(L)$, every $w\in L^*$, $1\le j\le n$ and $t>0$: if rank $j$ is ambiguous at $w$, then
--
--   $$\Delta_j(w)=\mathbb E_{G_t\sim\gamma_t}[h_j(w+G_t)]-\mathbb E_{G_{t/2}\sim\gamma_{t/2}}[h_j(w+G_{t/2})]\ge c\,t\lambda.$$
--
--   Ambiguity therefore costs a definite amount of heat.
--
--   Differences from the source:
--   - encoding: expectations over γ_a → the Bochner integral against the density ν_a; reason: h_j grows linearly, so the integrand is integrable and the value is the expectation
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Lemma 4.4, p.22

import Mathlib
import Definitions.Def_LIPAlgorithm_heatDelta

namespace LIPAlgorithm

/-- **Lemma 4.4 (Local heat lower bound).** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript sha256 61ee52aa…),
Lemma 4.4, p.22 (PDF p.25). If rank `j` is ambiguous at `w ∈ L*`, then `Δ_j(w) ≥ c·t·λ` for every `t > 0`, with an absolute
`c > 0`, placed before `n`, `L`, `w`, `j`, `t`. -/
theorem lemma_4_4 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L] (j : ℕ) (w : E n)
        (t : ℝ), 1 ≤ n → IsWellRounded L → 1 ≤ j → j ≤ n → w ∈ RegevLWE.GaussConv.dual L → 0 < t →
        Ambiguous L j w →
          c * t * RegevLWE.SmoothingLB.lambda1 L ≤ heatDelta L j t w := by sorry

end LIPAlgorithm
