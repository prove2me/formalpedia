-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_running_time
-- name    : NearlyOptimalPPR.Computation.recursive_running_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:39:22.539802+00:00
-- url     : https://prove2.me/theorems/5fb5d130-8263-4b2c-a1e5-73382c32c5f6
-- title:
--   Lemma 4.5 — Recursive running time
-- statement:
--   Fix the exact-SDDM model. There exist absolute $C,c>0$ chosen before every graph and parameter such that the following holds. Let $G$ be a finite simple unweighted undirected graph with a nonisolated seed $s$, real $0<\alpha\le1/2$ and $0<\varepsilon\le1$. Put
--
--   $$K=1/\varepsilon,\qquad\ell=\left\lfloor\sqrt{\frac{\log(2K)}{\log\log(4K)}}\right\rfloor,\qquad b=\left\lfloor N^{(\ell-j+1)/(\ell-j+2)}\right\rfloor.$$
--
--   Use this balanced block at each level $j$. The prescribed root call terminates and its actual charged work, equal to its expected value under the deterministic idealized solve charges, satisfies
--
--   $$\mathbb E W\le C K\exp\!\left(c\sqrt{\log(2K)\log\log(4K)}\right).$$
--
--   For every $\eta>0$, there is $0<\varepsilon_0\le1$ independent of $G,s,\alpha$ such that the displayed envelope is at most $K^{1+\eta}$ for $0<\varepsilon\le\varepsilon_0$. This states the full $K^{1+o(1)}$ bound; no fixed larger exponent replaces it.
--
--   The mathematical depth specifies this root-call analysis, not a free logarithm or square-root instruction in the goal's machine. Balanced blocks are obtained by the operational integer-power search, with preparation charged. Source-component completion and explicit output remain included in root work.
--
--   Differences from the source:
--   - encoding: K exp(O(sqrt(log(2K) log log(4K)))) = K^(1+o(1)) → uniform positive constants C,c and the full eventual exponent-1+eta assertion; reason: this makes both asymptotic quantifier orders explicit without changing their domain
--   - encoding: root call with the stated depth and balanced blocks → the operational root execution with the mathematically specified depth and charged integer block search; reason: depth selection is a parameter of this lemma; the existential goal machine must pay for all of its own parameter preparation
--   - encoding: expected root work → actual nonnegative root work under deterministic idealized solve charges; reason: these charges equal their expected values and nontermination is infinite
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Lemma 4.5 pp.18–19

import Mathlib
import Definitions.Def_NearlyOptimalPPR_Computation_push

set_option autoImplicit false

open Finset Matrix MeasureTheory
open scoped ENNReal

namespace NearlyOptimalPPR.Computation

/-- Li, Xu, Yang, Zhou, STOC 2027 submission #884 (October 2026),
Lemma 4.5 pp.18--19. Quantitative envelope and the full 1+o(1) assertion. -/
theorem recursive_running_time (m : SolveModel) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ subpolynomialEnvelope C c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ),
        0 < α → α ≤ 1 / 2 → 0 < ε → ε ≤ 1 → 0 < g.graph.degree s →
          let ℓ := balancedDepth ε
          recursiveWork m g s α ε ℓ [] ≤ ENNReal.ofReal (envelope C c ε) ∧
          ∃ t : ℕ, (recursiveRun m g s α (rootThreshold ε ℓ) ℓ [] t).done = true := by sorry

end NearlyOptimalPPR.Computation
