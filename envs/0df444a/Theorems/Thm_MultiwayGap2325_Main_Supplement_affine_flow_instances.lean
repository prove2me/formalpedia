-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_flow_instances
-- name    : MultiwayGap2325.Main.Supplement.affine_flow_instances
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:23:51.608213+00:00
-- url     : https://prove2.me/theorems/e29e8f3e-98b0-4ccf-a673-45265400aece
-- title:
--   Theorem 6.1 — Affine flow instances and exact integrals
-- statement:
--   Fix any integer $q\ge2$ and any real $T\in(1/2,1)$. For $2\le r\le q$ set
--
--   $$a_r=\frac{(rT-1)(r-2)!(q-r)!}{T^{r-2}q!}.$$
--
--   For every face $S$ of size $r\ge2$ take the single cell $\Omega_S$, and choose
--
--   $$p_s^S(x)=\frac{T-x_s}{rT-1},\quad F_i^S(x)=a_r(e_i-p^S(x)),\quad F_*^S=0,\quad
--   w_{st}^S=\frac{a_r}{r-1},\quad g_i^S=a_r.$$
--
--   Set $\epsilon^U=0$ for $U\ne[q]$ and $\epsilon^{[q]}=(q-1)a_q/(qT-1)$. These specified data form a valid flow instance. Its actual geometric integrals satisfy every identity below, with $z=(1-T)/T$:
--
--   $$B=\sum_{r=2}^q\frac{(rT-1)z^{r-2}}{(r-1)!}
--   =T\left(1-\frac{z^{q-1}}{(q-1)!}\right),$$
--   $$R=\frac{1-q(1-T)^{q-1}}{q!T^{q-2}},\qquad B-R=T-\frac1{q!T^{q-2}},$$
--   $$L=(1-T)B+\sum_{r=2}^q\frac{(rT-1)(1-r(1-T)^{r-1})}{2(r-1)(r-1)!T^{r-2}}.$$
--
--   This family includes $q=2$ and arbitrary real thresholds in the stated open interval. In particular, capacity, conservation, normal continuity and the terminal condition are conclusions for the explicitly constructed data. The theorem provides the complete affine family underlying the specialized existence result.
--
--   **Formalization Note** The named raw construction contains the formulas (23)–(24); the theorem equates the actual integrals with the expressions (25). The top-face allowance is integrated once and is not identified with its density.
--
--   Differences from the source:
--   - encoding: formulas (23)-(24) for the chosen data → the fixed raw function affineData q T with one cell on every face; reason: the construction is computed from q and T, with no validity or integral identity assumed
--   - encoding: integer ranges, factorials, and real divisions in (23)-(25) → Fin q coordinates, Finset.Icc 2 q sums, natural factorials cast to reals, and natural exponents in their valid ranges; reason: q >= 2 and 2 <= r <= q preserve all boundary cases and make the displayed denominators nonzero
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Theorem 6.1, p. 23

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

namespace MultiwayGap2325.Main.Supplement

/-- Theorem 6.1, p.23, equations (23)–(25). Every validity condition and integral identity
is asserted for the specified raw data, not assumed in the input. -/
theorem affine_flow_instances (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    let D := affineData q T
    IsFlowInstance T D ∧
    totalB T D.weighting = affineBSum q T ∧
    totalB T D.weighting = affineBClosed q T ∧
    totalR T D = affineRClosed q T ∧
    totalB T D.weighting - totalR T D = affineNetClosed q T ∧
    totalL T D.weighting = (1 - T) * totalB T D.weighting + affineInteriorClosed q T := by sorry

end MultiwayGap2325.Main.Supplement
