-- Prove2me | Theorems.Thm_MixedCloning_Optimal_lemma_17
-- name    : MixedCloning.Optimal.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:59.353591+00:00
-- url     : https://prove2.me/theorems/9fdb1e2f-8f50-4748-8e4e-06b05630903d
-- title:
--   Lemma 17 — expectation bound forces n ≥ krd/(8ε)
-- statement:
--   Let $d\ge2$, $r\ge1$, $2r\le d$, $k\ge1$ and $n\ge0$ be integers. Let $0<\varepsilon\le1/16$, and let $\lambda$ have the weak Schur sampling law for $n$ copies of the rank-$r$ maximally mixed state. If
--
--   $$1-\varepsilon\le\mathbb E_\lambda\left[\prod_{j=1}^k\frac{r+\lambda_1+j-1}{d+\lambda_1+j-1}\right],$$
--
--   then
--
--   $$n\ge\frac{krd}{8\varepsilon}.$$
--
--   This retains the explicit constant printed in the lemma and allows zero input copies. It converts the representation-theoretic upper bound on overlap into the quantitative sample lower bound.
--
--   Differences from the source:
--   - encoding: partitions and tableaux with symbols starting at 1 → YoungDiagram cells and Fin alphabets starting at 0; reason: shifting indices preserves all shapes, orders, counts and contents
--   - encoding: r ≤ d/2 and positive accuracy tolerance → 2r ≤ d and 0 < ε ≤ 1/16; reason: integer arithmetic and the domain on which the printed division is defined
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 20, Lemma 17

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_17 (d r n k : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : 2*r ≤ d)
    (hk : 1 ≤ k) (eps : ℝ) (heps : 0 < eps) (heps16 : eps ≤ 1/16)
    (h : 1-eps ≤ wssExpectation n r (extraProduct d r k)) :
    (k : ℝ)*r*d/(8*eps) ≤ n := by sorry

end MixedCloning.Optimal
