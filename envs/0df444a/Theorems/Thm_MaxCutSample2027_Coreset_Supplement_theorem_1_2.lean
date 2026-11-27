-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_Supplement_theorem_1_2
-- name    : MaxCutSample2027.Coreset.Supplement.theorem_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T10:01:54.899614+00:00
-- url     : https://prove2.me/theorems/753017f5-b03d-42c8-9314-a05003fae6eb
-- title:
--   Theorem 1.2 — general sampling distributions, explicit constant 2304
-- statement:
--   Let $A$ be a symmetric matrix on a finite nonempty vertex set of size $n$, with zero diagonal and weights in $[0,1]$. Let $p$ be any probability vector satisfying $p_v\ge d(v)/n^2$, where $d(v)=\sum_uA_{vu}$. Positivity is not assumed: a vertex of probability zero is necessarily isolated. For $0<\varepsilon<1$, $0<\delta<1$, and any natural sample size
--   $$k\ge2304\varepsilon^{-2}\delta^{-2},$$
--   independent sampling with replacement and reweighting $\widehat A_{ij}=A_{X_iX_j}/(k^2p_{X_i}p_{X_j})$ satisfy
--   $$\Pr\bigl(|\operatorname{MaxCut}(\widehat A)-\operatorname{MaxCut}(A)|\le\varepsilon n^2\bigr)\ge1-\delta.$$
--   This states the general bounded-weight sampling guarantee with an explicit absolute constant. Zero-probability outcomes have product-law weight zero; the totalized division on those outcomes does not affect the probability.
--
--   Differences from the source:
--   - generalization: a suitable absolute constant C > 0 → the explicit choice C = 2304; reason: the Corollary 2.2 estimate supplies 48², which recovers the asserted suitable-constant guarantee
--   - encoding: the probability of a sample event under independent draws with replacement → the finite product-law average of its indicator over Fin k sample positions; reason: each ordered sample has exactly its source probability, and the event retains the source strict or non-strict inequalities
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Theorem 1.2, p. 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_sampling
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

theorem theorem_1_2 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hbound : ∀ u v, A u v ≤ 1)
    (hp : IsProbabilityVector p)
    (hdegree : ∀ v, weightedDegree A v / (Fintype.card V : ℝ) ^ 2 ≤ p v)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (k : ℕ) (hsize : 2304 * ε ^ (-2 : ℤ) * δ ^ (-2 : ℤ) ≤ (k : ℝ)) :
    1 - δ ≤ eventProbability p k
      (fun x => |maxCut (Ahat A p x) - maxCut A| ≤ ε * (Fintype.card V : ℝ) ^ 2) := by sorry

end MaxCutSample2027.Coreset.Supplement
