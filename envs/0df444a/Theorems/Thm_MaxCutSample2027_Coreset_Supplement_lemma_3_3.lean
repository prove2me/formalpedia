-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_3_3
-- name    : MaxCutSample2027.Coreset.Supplement.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T10:02:38.508195+00:00
-- url     : https://prove2.me/theorems/72d2b5f0-0bf3-4056-ba26-8f4d94670d34
-- title:
--   Lemma 3.3 — comparison using sampled edges
-- statement:
--   Let $V$ be a finite nonempty set of size $n$, let $A$ be a symmetric nonnegative real matrix with zero diagonal, and let $p$ be a positive probability vector. Write $K_{uv}=A_{uv}/(n^2p_up_v)$ and $H=\sum_vp_v\sqrt{\sum_up_uK_{uv}^2}$. Sample positions are independent draws from $p$ with replacement; their empirical law is $P_X$, and the sampled graph on $[k]$ has weights $\widehat A_{ij}=A_{X_iX_j}/(k^2p_{X_i}p_{X_j})$.
--
--   For nonnegative $q$, $Z(q)=\{a:0\le a\le q\}$ and $F_K(q)=\max_{a\in Z(q)}a^\top K(q-a)$. The comparison quantity is $\Delta_K(q,s)=\max_{c\in C(q,s)}|M_q(c)-M_s(c)|$, with $C(q,s)=\operatorname{conv}(Z(q)\cup-Z(q)\cup Z(s)\cup-Z(s))$ and $M_q(c)=\max_{a\in Z(q)}a^\top Kc$. Let $k\ge1$, fix a sample $x$, and let $a\in Z(P_x)$ attain $F_K(P_x)$. Put $\Delta=\Delta_K(p,P_x)$ and $e_x(a,b)=k^{-1}\sum_i|(Ka)_{x_i}-(Kb)_{x_i}|$. Every $b\in Z(p)$ satisfies
--   $$b^\top K(p-b)\ge F_K(P_x)-4\Delta-e_x(a,b).$$
--   This is the deterministic comparison used by the recovery objective. The expectation law does not constrain the particular sample outcome in this statement.
--
--   Differences from the source:
--   - generalization: discard isolated vertices and assume d(v) > 0 in the standing setup → all symmetric nonnegative zero-diagonal matrices, including isolated vertices; reason: isolated vertices contribute zero; restricting to graphs with positive degrees recovers every source instance
--   - generalization: a represents an optimal cut of the sampled graph → any a in Z(P_X) attaining F_K(P_X), including fractional maximizers; reason: the source cut is among these maximizers; the comparison and recovery arguments on pp.17–18 use feasibility and the maximizing equality only
--   - encoding: the k sampled vertices and empirical frequencies → Fin k sample positions and finite empirical counts; reason: all k positions remain present, including repeated draws; the matrix-vector sums and errors are unchanged
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma 3.3, p. 17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_recovery
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

theorem lemma_3_3 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k)
    (x : Fin k → V) (a : V → ℝ) (ha : a ∈ Z (empirical x))
    (hopt : bilinear (K A p) a (empirical x - a) = FK (K A p) (empirical x))
    (b : V → ℝ) (hb : b ∈ Z p) :
    FK (K A p) (empirical x) - 4 * DeltaK (K A p) p (empirical x) -
      recoveryError (K A p) x a b ≤ bilinear (K A p) b (p - b) := by sorry

end MaxCutSample2027.Coreset.Supplement
