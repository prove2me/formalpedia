-- Prove2me | Theorems.Thm_MixedCloning_Optimal_wss_first_row
-- name    : MixedCloning.Optimal.wss_first_row
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:06:10.794974+00:00
-- url     : https://prove2.me/theorems/011f77dc-1af9-44df-865c-cc5e65c9cd9b
-- title:
--   Proof of Lemma 17 — expected first row under WSS
-- statement:
--   Let $n\ge0$ and $r\ge1$. Draw $\lambda$ by weak Schur sampling the maximally mixed rank-$r$ state, so that the probability of shape $\lambda\vdash n$ is $\dim(P_\lambda)s_\lambda(1^r)/r^n$. Then
--
--   $$\mathbb E[\lambda_1]\le n/r+2\sqrt n.$$
--
--   The expectation is the finite sum with these concrete tableau weights. This cited input controls the size parameter entering the cloning product bound; it is not assumed as part of the distribution's definition.
--
--   Differences from the source:
--   - encoding: partitions and tableaux with symbols starting at 1 → YoungDiagram cells and Fin alphabets starting at 0; reason: shifting indices preserves all shapes, orders, counts and contents
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 20, Proof of Lemma 17, citing [OW17, Theorem 5.2]

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem wss_first_row (n r : ℕ) (hr : 1 ≤ r) :
    wssExpectation n r (fun L => L.rowLen 0) ≤ (n : ℝ)/r + 2*Real.sqrt n := by sorry

end MixedCloning.Optimal
