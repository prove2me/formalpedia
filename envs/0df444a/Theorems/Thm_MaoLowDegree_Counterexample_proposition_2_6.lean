-- Prove2me | Theorems.Thm_MaoLowDegree_Counterexample_proposition_2_6
-- name    : MaoLowDegree.Counterexample.proposition_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:13.996897+00:00
-- url     : https://prove2.me/theorems/56614ff8-a7c2-401b-8763-53ffce6f9f27
-- title:
--   Proposition 2.6 — exact uniformity, including after noise
-- statement:
--   Fix the construction parameters and a valid family $P_n$, and let $n\ge n_0$. Write $D_\star=\lfloor L/2\rfloor$. For every edge subset $S\subseteq E_n$ with $|S|\le D_\star$ and every bit pattern $z$ on $S$,
--   $$\Pr_{X\sim P_n}[X|_S=z]=2^{-|S|}.$$
--   The same equality holds under $T_\varepsilon P_n$ for every $\varepsilon\in[0,1]$.
--
--   Thus all marginals on at most $D_\star$ distinct edges agree exactly with those of $Q_n$, both before and after noise. This includes the empty marginal and both endpoints of the resampling interval.
--
--   Differences from the source:
--   - encoding: vertices 1 through n and unordered edges → Fin n with increasing endpoint pairs; n=0 is an empty-cube extension; reason: relabeling by subtracting one changes no positive-n instance
--   - encoding: the fixed subspace, basis, points and planted family of Sections 2–3 → CodeData, Construction and ValidConstruction with explicit standing numerical hypotheses; reason: expands the section preamble without assuming a graph-law conclusion
--   - encoding: uniform on t distinct edges for every t at most D_star → all patterns on every Finset of at most D_star unordered edges; reason: equivalent exact coordinate marginal formulation
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), Proposition 2.6, p.10; fixed choices, pp.8–10

import Definitions.Def_MaoLowDegree_Counterexample_computationalClaims

open Classical Filter
open scoped Topology
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- Proposition 2.6, p.10. Exact marginals, including both endpoints of the noise interval. -/
theorem proposition_2_6 (r : ℕ) (β₁ β₂ b κ : ℝ)
    (hparams : Admissible r β₁ β₂ b κ) (C : Construction r b κ)
    (hC : ValidConstruction β₁ C) (n : ℕ) (hn : C.n₀ ≤ n) :
    MarginalUniform (constructedFamily C n) (starDegree r b κ n) ∧
      ∀ ε : Rate, MarginalUniform (noise ε (constructedFamily C n)) (starDegree r b κ n) := by sorry

end MaoLowDegree.Counterexample
