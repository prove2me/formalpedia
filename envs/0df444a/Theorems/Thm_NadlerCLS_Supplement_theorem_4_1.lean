-- Prove2me | Theorems.Thm_NadlerCLS_Supplement_theorem_4_1
-- name    : NadlerCLS.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:55:35.519831+00:00
-- url     : https://prove2.me/theorems/085e77fb-c83f-415f-b643-fb36db7ed4fb
-- title:
--   Theorem 4.1 — strong converse to Nadler's theorem
-- statement:
--   Let $(X,d)$ be a compact metric space, and let $F:X\to\mathcal K(X)$ be a Hausdorff-continuous correspondence with nonempty compact values. Suppose $x^*$ is an endpoint, so $F(x^*)=\{x^*\}$, and suppose:
--
--   1. for every $x\in X$, the full reachable set $F^{[t]}(x)$ converges in Hausdorff distance to $\{x^*\}$ as $t\to\infty$;
--   2. this convergence is uniform for $x$ in some open neighborhood of $x^*$.
--
--   Then, for every contraction factor $c\in(0,1)$ and every accuracy scale $\varepsilon>0$, there is a metric $D_{c,\varepsilon}$ on $X$ such that:
--
--   1. $D_{c,\varepsilon}$ and $d$ generate the same topology, and $(X,D_{c,\varepsilon})$ is compact and complete;
--   2. for all $x,y\in X$,
--      $$H_{D_{c,\varepsilon}}(F(x),F(y))\le cD_{c,\varepsilon}(x,y);$$
--   3. the quantitative transfers
--      $$D_{c,\varepsilon}(x,x^*)\le\varepsilon\Longrightarrow d(x,x^*)\le2\varepsilon,$$
--      $$D_{c,\varepsilon}(x,y)\le\varepsilon\Longrightarrow
--      \min\{d(x,y),d(x,x^*),d(y,x^*)\}\le2\varepsilon$$
--      hold.
--
--   Thus every compact-valued iteration satisfying the paper's robust and locally uniform convergence hypotheses can be remetrized as a Hausdorff contraction without losing the original topology or its quantitative notion of approximation.
--
--   Differences from the source:
--   - encoding: Hausdorff distance, convergence, metric topology, compactness, and completeness are stated with their standard metric-space notation → Hausdorff inequalities are unfolded into both directed pointwise bounds, convergence into epsilon statements, and the new metric's topology, compactness, and completeness into explicit predicates; reason: this compares two metrics on one Lean type without changing the installed reference metric, and is equivalent for the nonempty compact sets in the theorem
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Theorem 4.1, p.12; equations (4.1)–(4.5), p.12; proof pp.48–53

import Mathlib
import Definitions.Def_NadlerCLS_Supplement_HausdorffBound

set_option autoImplicit false

namespace NadlerCLS

namespace Supplement

/-- **Theorem 4.1 (strong converse to Nadler's theorem).**
(Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256
1fcc5a02…6dc485, Theorem 4.1, p.12.)

Let `X` be compact, let `F` be a nonempty compact-valued Hausdorff-continuous correspondence,
and suppose `xstar` is an endpoint.  If all reachable sets converge robustly to `xstar` as in
(4.1), locally uniformly as in (4.2), then for every `c ∈ (0,1)` and `epsilon > 0` there is a
topologically equivalent compact complete metric `D` under which `F` is a Hausdorff
`c`-contraction.  Both quantitative transfers (4.4) and (4.5) hold with the printed constant `2`.

**Formalization Note** Compact-valued means nonempty and compact, exactly the paper's `K(X)`.
Hausdorff inequalities are unfolded as two directed pointwise bounds, which are equivalent for
the nonempty compact sets here.  Convergence is written in its epsilon form.  `CompactFor`,
`CompleteFor`, and `GeneratesSameTopology` explicitly express the three properties of the new
metric without replacing the original metric-space instance. -/
theorem theorem_4_1 {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X → Set X) (xstar : X)
    (hF_nonempty : ∀ x, (F x).Nonempty)
    (hF_compact : ∀ x, IsCompact (F x))
    (hF_continuous : HausdorffContinuous F)
    (hendpoint : F xstar = {xstar})
    (hglobal : RobustlyGloballyConverges F xstar)
    (hlocal : LocallyUniformlyConverges F xstar)
    (c epsilon : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hepsilon : 0 < epsilon) :
    ∃ D : X → X → ℝ,
      IsMetricFunction D ∧
      GeneratesSameTopology D ∧
      CompactFor D ∧
      CompleteFor D ∧
      (∀ x y, HausdorffBound D (F x) (F y) (c * D x y)) ∧
      (∀ x, D x xstar ≤ epsilon → dist x xstar ≤ 2 * epsilon) ∧
      (∀ x y, D x y ≤ epsilon →
        min (dist x y) (min (dist x xstar) (dist y xstar)) ≤ 2 * epsilon) := by sorry

end Supplement

end NadlerCLS
