-- Prove2me | Theorems.Thm_MixedCloning_Optimal_lemma_19
-- name    : MixedCloning.Optimal.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:54.977005+00:00
-- url     : https://prove2.me/theorems/bc9e4ab1-d9a1-4eec-88a6-79f0398481fb
-- title:
--   Lemma 19 — partially transposed integral bound
-- statement:
--   Let $1\le r\le d$ and let $\lambda,\mu$ be arbitrary diagrams of height at most $d$. For normalized Haar measure on rank-$r$ orthogonal projectors, and in any orthonormal bases of the Schur modules,
--
--   $$\int q_\lambda(P)^T\otimes q_\mu(P)\,dP\preceq\frac{s_{\lambda\cup\mu}(1^r)}{s_{\lambda\cup\mu}(1^d)}I_\lambda\otimes I_\mu.$$
--
--   There are no restrictions on the sizes of the diagrams or on their heights relative to $r$; when either height exceeds $r$, both sides vanish. This is the Lemma 19 form, which includes all cases of Lemma 15 and supplies the spectral bound used by the cloning lower bound.
--
--   Differences from the source:
--   - generalization: transpose in the Schur basis → transpose in any orthonormal basis of each Schur module; reason: unitary changes of basis conjugate the partially transposed operator and preserve its order and operator norm
--   - encoding: partitions and tableaux with symbols starting at 1 → YoungDiagram cells and Fin alphabets starting at 0; reason: shifting indices preserves all shapes, orders, counts and contents
--   - encoding: Φ symbol after the equality → the explicit Schur-count ratio alone; reason: Φ is an abbreviation for that ratio and is not separately defined in the paper
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 21, Lemma 19

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_19 (d r : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d)
    (L M : YoungDiagram) (hL : height L ≤ d) (hM : height M ≤ d)
    (b : SchurBasis L d) (c : SchurBasis M d) :
    (((ratio (L ⊔ M) r d : ℂ) • 1) - transposedIntegral r L M b c).PosSemidef := by sorry

end MixedCloning.Optimal
