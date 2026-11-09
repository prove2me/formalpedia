-- Prove2me | Theorems.Thm_MixedCloning_Optimal_lemma_9
-- name    : MixedCloning.Optimal.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:53.000263+00:00
-- url     : https://prove2.me/theorems/d967ef25-6e82-48f8-9bb2-ee4fde2d4001
-- title:
--   Lemma 9 — monotonicity of the Schur dimension ratio
-- statement:
--   Let $\sigma\subseteq\tau$ be Young diagrams of height at most $d$, and let $1\le t\le d$. For $s_\lambda(1^t)$ the semistandard-tableau count on an alphabet of size $t$,
--
--   $$\frac{s_\sigma(1^t)}{s_\sigma(1^d)}\ge\frac{s_\tau(1^t)}{s_\tau(1^d)}.$$
--
--   The numerator is zero when the diagram has more than $t$ rows. This monotonicity applies even in that regime and compares the coefficients needed in the separability recursion.
--
--   Differences from the source:
--   - encoding: partitions and tableaux with symbols starting at 1 → YoungDiagram cells and Fin alphabets starting at 0; reason: shifting indices preserves all shapes, orders, counts and contents
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 14, Lemma 9

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_9 (d t : ℕ) (ht : 1 ≤ t) (htd : t ≤ d)
    (S T : YoungDiagram) (hS : height S ≤ d) (hT : height T ≤ d) (hST : S ≤ T) :
    ratio T t d ≤ ratio S t d := by sorry

end MixedCloning.Optimal
