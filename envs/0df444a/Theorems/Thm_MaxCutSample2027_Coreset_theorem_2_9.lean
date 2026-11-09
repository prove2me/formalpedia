-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_theorem_2_9
-- name    : MaxCutSample2027.Coreset.theorem_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:48:20.526316+00:00
-- url     : https://prove2.me/theorems/48a2dff5-10c1-4463-acae-bec295701910
-- title:
--   Theorem 2.9 — expected error in the fractional cut functional
-- statement:
--   Let $V$ be a finite nonempty vertex set, $n=|V|$, and let $A:V\times V\to\mathbb R$ be symmetric with zero diagonal and nonnegative entries. Let $p$ satisfy $p_v>0$ for every vertex and $\sum_vp_v=1$. Define $K_{uv}=A_{uv}/(n^2p_up_v)$. Write $H=\sum_vp_v\sqrt{\sum_up_uK_{uv}^2}$.
--
--   For a nonnegative vector $r$, write $Z(r)=\{a\in\mathbb R^V:0\le a_v\le r_v\text{ for every }v\}$ and $F_K(r)=\max_{a\in Z(r)}a^\top K(r-a)$, where $a^\top Kc=\sum_{u,v}a_uK_{uv}c_v$.
--
--   For an integer $k\ge1$, let $X=(X_0,\ldots,X_{k-1})$ be independent draws with replacement from $p$, and let $P_X(v)=|\{i:X_i=v\}|/k$.
--
--   Then
--   $$\mathbb E_X|F_K(P_X)-F_K(p)|\le\frac{48H}{\sqrt{k}}.$$
--   This is the complete expected-error estimate for the fractional cut functional at the empirical and original distributions.
--
--   **Formalization Note** Every real supremum here is an attained maximum of a continuous function on a nonempty compact domain. Any expectation is an explicit finite product-law sum.
--
--   Differences from the source:
--   - generalization: the standing assumption d(v)>0 for every vertex → isolated vertices are allowed; reason: no quantity or step of §2.2–§2.4 divides by a degree; imposing positive degrees recovers every source instance
--   - encoding: iid sample expectation and fractional maxima → the finite product-law average on Fin k and compact-image real suprema; reason: the same sample distribution is used and both nonnegative boxes have attained extrema
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Theorem 2.9, equation (2.24), p. 14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Definitions.Def_MaxCutSample2027_Coreset_fractional
open scoped BigOperators

namespace MaxCutSample2027.Coreset

theorem theorem_2_9 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k) :
    sampleAverage p k (fun x => |FK (K A p) (empirical x) - FK (K A p) p|) ≤
      48 * H A p / Real.sqrt (k : ℝ) := by sorry

end MaxCutSample2027.Coreset
