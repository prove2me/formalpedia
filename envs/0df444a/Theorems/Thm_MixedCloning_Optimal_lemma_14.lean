-- Prove2me | Theorems.Thm_MixedCloning_Optimal_lemma_14
-- name    : MixedCloning.Optimal.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:09:54.320419+00:00
-- url     : https://prove2.me/theorems/e10e4f84-3ee9-403c-a6f6-9b3f01dfa4b8
-- title:
--   Lemma 14 — overlap bounded by Schur integrals
-- statement:
--   Let $1\le r\le d$, and let $C$ be a permutation-invariant channel from $n$ to $m$ copies. Put $\rho=P/r$ for a rank-$r$ projector $P$. In any orthonormal bases for the Schur modules,
--
--   $$\min_P\operatorname{tr}(C(\rho^{\otimes n})P^{\otimes m})\le\sum_{\lambda\vdash n,\ell(\lambda)\le r}\frac{\dim P_\lambda\,s_\lambda(1^d)}{r^n}\max_{\mu\vdash m,\ell(\mu)\le r}\left\|\int q_\lambda(P)^T\otimes q_\mu(P)\,dP\right\|_\infty.$$
--
--   Here Haar measure is normalized and the norm is the Hilbert-space operator norm. This converts the operational cloning problem into an estimate for explicit representation-theoretic integrals.
--
--   Differences from the source:
--   - generalization: transpose in the Schur basis → transpose in any orthonormal basis of each Schur module; reason: unitary changes of basis conjugate the partially transposed operator and preserve its order and operator norm
--   - encoding: minimum over rank-r projectors → existence of a rank-r projector with overlap bounded by the right side; reason: the overlap is continuous on the nonempty compact rank-r projector orbit
--   - encoding: maximum over partitions → real supremum of the finite nonempty set of norms; reason: r ≥ 1 ensures a one-row partition for every m, so this is an attained maximum
--   - generalization: the section uses m=n+k → arbitrary n,m ≥ 0; reason: the Choi and permutation argument does not require m>n
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 18, Lemma 14

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_14 (d r n m : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d)
    (C : Cloner d n m) (hC : QAlgorithms.IsChannel C) (hperm : PermInvariant d n m C)
    (b : (L : YoungDiagram) → SchurBasis L d) :
    ∃ P : Op (Fin d), IsProjector r P ∧
      overlap d r n m C P ≤
        ∑ L ∈ partitions n r, (spechtDim L : ℝ) * schurCount L d / (r : ℝ)^n *
          sSup ((partitions m r).image fun M => operatorNorm (transposedIntegral r L M (b L) (b M))) := by sorry

end MixedCloning.Optimal
