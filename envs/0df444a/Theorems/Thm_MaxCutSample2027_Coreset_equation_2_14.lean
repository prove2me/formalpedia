-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_equation_2_14
-- name    : MaxCutSample2027.Coreset.equation_2_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:48:34.937196+00:00
-- url     : https://prove2.me/theorems/aedfa431-84b9-48fe-981c-76a35835c742
-- title:
--   §2.4, eq. (2.14) — expected comparison gap
-- statement:
--   Let $V$ be a finite nonempty vertex set, $n=|V|$, and let $A:V\times V\to\mathbb R$ be symmetric with zero diagonal and nonnegative entries. Let $p$ satisfy $p_v>0$ for every vertex and $\sum_vp_v=1$. Define $K_{uv}=A_{uv}/(n^2p_up_v)$. Write $H=\sum_vp_v\sqrt{\sum_up_uK_{uv}^2}$.
--
--   For a nonnegative vector $r$, write $Z(r)=\{a\in\mathbb R^V:0\le a_v\le r_v\text{ for every }v\}$ and $F_K(r)=\max_{a\in Z(r)}a^\top K(r-a)$, where $a^\top Kc=\sum_{u,v}a_uK_{uv}c_v$.
--
--   For a nonnegative vector $q$, set $M_q(c)=\max_{a\in Z(q)}a^\top Kc$. For probability vectors $r,s$ (nonnegative coordinates summing to one), set $\mathcal C(r,s)=\operatorname{conv}(Z(r)\cup(-Z(r))\cup Z(s)\cup(-Z(s)))$ and $\Delta_K(r,s)=\max_{c\in\mathcal C(r,s)}|M_r(c)-M_s(c)|$.
--
--   For an integer $k\ge1$, let $X=(X_0,\ldots,X_{k-1})$ be independent draws with replacement from $p$, and let $P_X(v)=|\{i:X_i=v\}|/k$.
--
--   Then
--   $$\mathbb E_X\Delta_K(p,P_X)\le\frac{12H}{\sqrt{k}}.$$
--   This is the expected comparison-gap bound opening §2.4, with its stated constant twelve.
--
--   **Formalization Note** Every real supremum here is an attained maximum of a continuous function on a nonempty compact domain. Any expectation is an explicit finite product-law sum.
--
--   Differences from the source:
--   - generalization: the standing assumption d(v)>0 for every vertex → isolated vertices are allowed; reason: no quantity or step of §2.2–§2.4 divides by a degree; imposing positive degrees recovers every source instance
--   - encoding: iid sample expectation and the comparison maximum → the finite product-law average on Fin k and compact-image real suprema; reason: the same sample distribution is used and all comparison extrema are finite and attained
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), §2.4, eq. (2.14), p. 11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Definitions.Def_MaxCutSample2027_Coreset_fractional
open scoped BigOperators

namespace MaxCutSample2027.Coreset

theorem equation_2_14 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k) :
    sampleAverage p k (fun x => DeltaK (K A p) p (empirical x)) ≤
      12 * H A p / Real.sqrt (k : ℝ) := by sorry

end MaxCutSample2027.Coreset
