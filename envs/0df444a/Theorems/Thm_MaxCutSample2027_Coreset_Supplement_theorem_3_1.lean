-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_Supplement_theorem_3_1
-- name    : MaxCutSample2027.Coreset.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:04:09.927773+00:00
-- url     : https://prove2.me/theorems/512ede67-a8ec-458d-a4ee-9951a47f7b73
-- title:
--   Theorem 3.1 — cut recovery and at most nk adjacency queries
-- statement:
--   Let $V$ be a finite nonempty set of size $n$, let $A$ be a symmetric nonnegative real matrix with zero diagonal, and let $p$ be a positive probability vector. Write $K_{uv}=A_{uv}/(n^2p_up_v)$ and $H=\sum_vp_v\sqrt{\sum_up_uK_{uv}^2}$. Sample positions are independent draws from $p$ with replacement; their empirical law is $P_X$, and the sampled graph on $[k]$ has weights $\widehat A_{ij}=A_{X_iX_j}/(k^2p_{X_i}p_{X_j})$. For every $k\ge1$, let $S(x)\subseteq[k]$ be any optimal cut of $\widehat A(x)$, and set $a_v(x)=|\{i\in S(x):x_i=v\}|/k$. Let $b(x)\in Z(p)$ be any minimizer of $k^{-1}\sum_i|(Ka(x))_{x_i}-(Kb(x))_{x_i}|$, equivalently the $b$ component of an optimal solution of LP (3.6). Include every $v$ in the output cut $U$ independently with probability $b_v(x)/p_v$. Then
--   $$\mathbb E_{X,U}\frac{\operatorname{MaxCut}(A)-\operatorname{Cut}_A(U)}{n^2}\le\frac{120H}{\sqrt k}.$$
--   Admissible pairs $(S,b)$ exist for every sample, and the bound holds for every selection of them. Moreover $Q_x=\{(x_i,v):i\in[k],v\in V\}$ has at most $nk$ entries. For any other symmetric nonnegative zero-diagonal matrix $A'$ agreeing with $A$ on those entries, the sets of admissible pairs $(S,b)$ for $A$ and $A'$ are identical. Thus the algorithm is determined by at most $nk$ adjacency queries, with $p$ and sampling access provided as on p.17.
--   This keeps the recovery guarantee and query-locality conclusion together.
--
--   Differences from the source:
--   - generalization: discard isolated vertices and assume d(v) > 0 in the standing setup → all symmetric nonnegative zero-diagonal matrices, including isolated vertices; reason: isolated vertices contribute zero; restricting to graphs with positive degrees recovers every source instance
--   - encoding: expectation under k independent vertex draws with replacement → the explicit finite product-law sum over Fin k sample positions; reason: the sum gives exactly the source sampling law, including distinct positions for repeated draws
--   - encoding: LP (3.6), independent rounding, and at most nk adjacency queries → minimizers of (3.4), a finite product rounding law, and a query-cardinality plus admissible-input invariance conjunct; reason: eliminating optimal slack variables preserves exactly the b minimizers; the finite law and queried entries implement the stated algorithm; admissible choices are also asserted to exist
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Theorem 3.1, p. 16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_recovery
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

theorem theorem_3_1 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k)
    : (∀ x : Fin k → V, ∃ (S : Finset (Fin k)) (b : V → ℝ),
        AdmissibleRecovery A p x S b) ∧
      (∀ (S : (Fin k → V) → Finset (Fin k)) (b : (Fin k → V) → V → ℝ),
        (∀ x, AdmissibleRecovery A p x (S x) (b x)) →
        sampleAverage p k (fun x => roundedLoss A p (b x)) ≤
          120 * H A p / Real.sqrt (k : ℝ)) ∧
      (∀ x : Fin k → V,
        (queryEntries x).card ≤ Fintype.card V * k ∧
        ∀ (A' : V → V → ℝ), IsWeightMatrix A' →
          (∀ i v, A' (x i) v = A (x i) v) →
          ∀ (S : Finset (Fin k)) (b : V → ℝ),
            (AdmissibleRecovery A p x S b ↔ AdmissibleRecovery A' p x S b)) := by sorry

end MaxCutSample2027.Coreset.Supplement
