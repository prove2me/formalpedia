-- Prove2me | Theorems.Thm_MixedCloning_Optimal_proposition_20
-- name    : MixedCloning.Optimal.proposition_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:24.129206+00:00
-- url     : https://prove2.me/theorems/8fdc07cb-df90-4772-9c72-e3b3f00ebf2f
-- title:
--   Proposition 20 — separability of the integral defect
-- statement:
--   Let $1\le r\le d$ and let $\lambda,\mu$ be arbitrary Young diagrams of height at most $d$. In any orthonormal bases, define
--
--   $$\Delta_{\lambda\mu}=\frac{s_{\lambda\cup\mu}(1^r)}{s_{\lambda\cup\mu}(1^d)}I_\lambda\otimes I_\mu-\int q_\lambda(P)\otimes q_\mu(P)\,dP.$$
--
--   Then $\Delta_{\lambda\mu}$ is a finite nonnegative linear combination of matrices $A\otimes B$ with $A,B\succeq0$. The assertion includes diagrams of height greater than $r$, where the defect is zero. This stronger statement controls partial transposition, which does not preserve the positive cone in general.
--
--   Differences from the source:
--   - generalization: operators on the Schur modules → matrices in any orthonormal bases; reason: separability is invariant under local unitary changes of coordinates
--   - encoding: partitions and tableaux with symbols starting at 1 → YoungDiagram cells and Fin alphabets starting at 0; reason: shifting indices preserves all shapes, orders, counts and contents
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 21, Proposition 20; restated as Proposition 24 on p. 25

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem proposition_20 (d r : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d)
    (L M : YoungDiagram) (hL : height L ≤ d) (hM : height M ≤ d)
    (b : SchurBasis L d) (c : SchurBasis M d) :
    Separable (delta r L M b c) := by sorry

end MixedCloning.Optimal
