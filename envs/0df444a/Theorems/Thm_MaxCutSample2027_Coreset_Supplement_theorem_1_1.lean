-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_Supplement_theorem_1_1
-- name    : MaxCutSample2027.Coreset.Supplement.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:01:23.522961+00:00
-- url     : https://prove2.me/theorems/4cc1f6d8-0ecf-45dd-93a1-cfb7edc090b6
-- title:
--   Theorem 1.1 — uniform sampling, explicit constant 48
-- statement:
--   Let $V$ be a finite nonempty vertex set of size $n$, and let $A$ be symmetric with zero diagonal and weights in $[0,1]$. For every integer $k\ge1$, sample $X_1,\ldots,X_k$ independently and uniformly from $V$. On the $k$ distinct sample positions set $\widehat A_{ij}=(n/k)^2A_{X_iX_j}$. Then
--   $$\mathbb E|\operatorname{MaxCut}(\widehat A)-\operatorname{MaxCut}(A)|\le\frac{48n^2}{\sqrt k}.$$
--   Both optima are genuine maxima over all subsets of their vertex sets. The bound gives an explicit absolute constant for the source's uniform-sampling error rate.
--
--   Differences from the source:
--   - generalization: an absolute O(n²/√k) error bound → the explicit uniform bound 48 n²/√k; reason: Theorem 2.1 and Lemma 2.10 supply 48, which implies the full O-form with an absolute constant
--   - encoding: expectation under k independent vertex draws with replacement → the explicit finite product-law sum over Fin k sample positions; reason: the sum gives exactly the source sampling law, including distinct positions for repeated draws
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Theorem 1.1, p. 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_sampling
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

theorem theorem_1_1 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (hA : IsWeightMatrix A) (hbound : ∀ u v, A u v ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) :
    sampleAverage (uniformLaw (V := V)) k
      (fun x => |maxCut (Ahat A uniformLaw x) - maxCut A|) ≤
      48 * (Fintype.card V : ℝ) ^ 2 / Real.sqrt (k : ℝ) := by sorry

end MaxCutSample2027.Coreset.Supplement
