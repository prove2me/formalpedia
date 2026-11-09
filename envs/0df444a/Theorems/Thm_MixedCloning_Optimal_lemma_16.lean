-- Prove2me | Theorems.Thm_MixedCloning_Optimal_lemma_16
-- name    : MixedCloning.Optimal.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:58.800072+00:00
-- url     : https://prove2.me/theorems/a2015478-0e1c-4bf7-83e4-fd761769ddd9
-- title:
--   Lemma 16 — maximizing diagram and product formula
-- statement:
--   Let $1\le r\le d$, $k\ge0$, and let $\lambda\vdash n$ have height at most $r$. Among every $\mu\vdash n+k$ of height at most $d$, the ratio $s_{\lambda\cup\mu}(1^r)/s_{\lambda\cup\mu}(1^d)$ is maximized by $\mu=\lambda+ke_1$. This diagram is admissible, and its value is
--
--   $$\frac{s_{\lambda\cup(\lambda+ke_1)}(1^r)}{s_{\lambda\cup(\lambda+ke_1)}(1^d)}=\frac{s_\lambda(1^r)}{s_\lambda(1^d)}\prod_{j=1}^k\frac{r+\lambda_1+j-1}{d+\lambda_1+j-1}.$$
--
--   Competitors with height greater than $r$ are included and have ratio zero. Both maximization and evaluation are asserted, giving an explicit bound on the Schur-integral optimization.
--
--   Differences from the source:
--   - encoding: partitions and tableaux with symbols starting at 1 → YoungDiagram cells and Fin alphabets starting at 0; reason: shifting indices preserves all shapes, orders, counts and contents
--   - generalization: the cloning section uses k ≥ 1 → k ≥ 0; reason: the empty-product case also gives exactly the stated maximum
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 19, Lemma 16

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_16 (d r n k : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d)
    (L : YoungDiagram) (hsize : L.card = n) (hL : height L ≤ r) :
    ((addTop L k).card = n+k ∧ height (addTop L k) ≤ d) ∧
    (∀ M : YoungDiagram, M.card = n+k → height M ≤ d →
      ratio (L ⊔ M) r d ≤ ratio (L ⊔ addTop L k) r d) ∧
    ratio (L ⊔ addTop L k) r d = ratio L r d * extraProduct d r k L := by sorry

end MixedCloning.Optimal
