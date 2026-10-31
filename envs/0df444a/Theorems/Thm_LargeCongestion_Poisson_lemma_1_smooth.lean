-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_lemma_1_smooth
-- name    : LargeCongestion.Poisson.lemma_1_smooth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:16.158673+00:00
-- url     : https://prove2.me/theorems/aff3b70d-f38c-4612-acde-49307b49b60a
-- title:
--   Lemma 1 (first sentence), p. 18 — under (18) the costs c̆_e are finite and C² on [0, d_max] with 0 ≤ c̆′_e(x) ≤ ζ
-- statement:
--   Let the costs $c_e$ be nonnegative and weakly increasing on $\mathbb N^*$, and assume the moment part of (18): $\mathsf E[|\Delta^2 c_e(1+V)|] \le \nu$ for every resource $e$, $V \sim \mathrm{Poisson}(d_{\max})$, with $d_{\max} > 0$. Let $\zeta = (e^{d_{\max}} - 1)\nu + \max_e(c_e(2) - c_e(1))$ (19). Then for every $e$ the auxiliary cost $\breve c_e(x) = \mathsf E[c_e(1+X)]$, $X \sim \mathrm{Poisson}(x)$, is finite for $x \in [0, d_{\max}]$, of class $C^2$ on $[0, d_{\max}]$, and
--   $$0 \le \breve c_e'(x) \le \zeta \qquad \text{for all } x \in [0, d_{\max}] .$$
--
--   In particular $\breve c_e$ is nondecreasing and $\zeta$-Lipschitz on the range of loads that matter, which makes the limit game $\breve\Gamma^\infty$ well posed.
--
--   **Formalization Note** Finiteness is the summability of $k \mapsto c_e(1+k)\mathsf P(X = k)$; smoothness and derivatives are relative to $[0, d_{\max}]$. Condition (18) gives $d_{\max} > d_{\mathrm{tot}} \ge 0$; here only $d_{\max} > 0$ and the moment bound are assumed, which is equivalent for this statement because the demands do not appear in it.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, p. 18, Lemma 1 (first sentence), (18), (19)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus
import Definitions.Def_LargeCongestion_Poisson_Game

namespace LargeCongestion.Poisson

open MeasureTheory ProbabilityTheory

/-- Lemma 1, first sentence, p. 18: under (18) the auxiliary costs `c̆_e` are finite and of class
`C²` on `[0, d_max]` with `0 ≤ c̆′_e(x) ≤ ζ` for all `x ∈ [0, d_max]`. Condition (18) enters as its
moment part and `d_max > 0` (which (18) gives, as `d_max > d_tot ≥ 0`). -/
theorem lemma_1_smooth {E : Type*} [Fintype E] [DecidableEq E] (c : E → ℕ → ℝ)
    (hc : IsCostFamily c) (ν dmax : ℝ) (hd : 0 < dmax) (hM : MomentBound c ν dmax) (e : E) :
    (∀ x ∈ Set.Icc 0 dmax, Summable (fun k : ℕ => c e (1 + k) * poissonPmf x k)) ∧
      ContDiffOn ℝ 2 (cBreve c e) (Set.Icc 0 dmax) ∧
      ∀ x ∈ Set.Icc 0 dmax,
        0 ≤ derivWithin (cBreve c e) (Set.Icc 0 dmax) x ∧
          derivWithin (cBreve c e) (Set.Icc 0 dmax) x ≤ zeta c ν dmax := by sorry

end LargeCongestion.Poisson
