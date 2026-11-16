-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_Supplement_lemma_3_6
-- name    : MoneyBurningTrade.IndependentSurplus.Supplement.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:39:54.011211+00:00
-- url     : https://prove2.me/theorems/885ece36-2b27-4154-87ed-566440d5b0b4
-- title:
--   Lemma 3.6 — allocation inequality from DSIC, IR and WBB
-- statement:
--   Let the common value space $V\subseteq\mathbb R_{\ge0}$ be an interval, and let $M=(x,p_B,p_S)$ be a measurable randomized mechanism on $V$ that is dominant-strategy incentive compatible, individually rational and weakly budget balanced. Then for all $v_s,v_b\in V$ with $v_s\le v_b$ (equality included),
--
--   $$\int_{v_s}^{v_b}x(z,v_b)\,dz+\int_{v_s}^{v_b}x(v_s,z)\,dz\le(v_b-v_s)\cdot x(v_s,v_b).\tag{8}$$
--
--   The inequality is the paper's basic consequence of Myerson's lemma and weak budget balance; it drives the impossibility results of §5 (Lemmas 5.4 and 5.8).
--
--   **Formalization Note** The value space is an order-connected subset $T$ of $[0,\infty)$; the integrals are oriented interval integrals over $[v_s,v_b]\subseteq T$.
--
--   Differences from the source:
--   - encoding: an interval value space V ⊆ ℝ≥0 → an order-connected set T ⊆ [0, ∞); reason: the order-connected subsets of ℝ are exactly its intervals
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 3.6, inequality (8); §3.2, printed p. 15 (PDF p. 16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsDSIC
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsIR
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsWBB

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- Lemma 3.6, §3.2 p.15, inequality (8): on any interval value space `T ⊆ ℝ≥0`,
a DSIC, IR, WBB mechanism satisfies, for all `v_s ≤ v_b` in `T` (equality included),
`∫_{v_s}^{v_b} x(z, v_b) dz + ∫_{v_s}^{v_b} x(v_s, z) dz ≤ (v_b − v_s)·x(v_s, v_b)`. -/
theorem lemma_3_6 (T : Set ℝ) (hT0 : T ⊆ Set.Ici 0) (hT : T.OrdConnected)
    (M : SecondBestBT.Mechanism)
    (hM : IsMechanism T M) (hdsic : IsDSIC T M) (hir : IsIR T M) (hwbb : IsWBB T M)
    (vs vb : ℝ) (hvs : vs ∈ T) (hvb : vb ∈ T) (hle : vs ≤ vb) :
    (∫ z in vs..vb, M.x (z, vb)) + (∫ z in vs..vb, M.x (vs, z)) ≤
      (vb - vs) * M.x (vs, vb) := by sorry

end MoneyBurningTrade.IndependentSurplus.Supplement
