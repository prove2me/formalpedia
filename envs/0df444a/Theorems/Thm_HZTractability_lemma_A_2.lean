-- Prove2me | Theorems.Thm_HZTractability_lemma_A_2
-- name    : HZTractability.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:10:25.820797+00:00
-- url     : https://prove2.me/theorems/3e42edba-4c7b-407e-9220-112617f02b3e
-- title:
--   Lemma A.2 — supply and population inequalities
-- statement:
--   Under the standing assumptions of Appendix A ($a=A/D\in(0,1)$ in lowest terms, $C=16D^2$, $b=4C$, $0<\tau\le\kappa/100$, $K$ admissible), at each vertex with degree pair $h_v\in\{0,1,2\}$, $o_v\in\{1,2\}$:
--
--   1. the low supply satisfies (29):
--   $$
--   o_vK<S_L<o_vK+b_v,\qquad \frac{o_vK+b_v}{S_L}<aL;
--   $$
--   2. $c_v>b+1$, $aL\,S_M>c_v+10$, and $\dfrac{3(b+1)(1+a)}{K}<1$;
--   3. $L\,S_H>10$ and $(L+\eta)S_H<c_v$;
--   4. in particular $c_v>b_v$ and $aL\,S_M>b_v$.
--
--   These inequalities drive the price chain of the exact analysis and its robust version in Appendix B.
--
--   Differences from the source:
--   - encoding: $a=A/D$ in lowest terms and $K$ a positive multiple of $D^2(D^2-A^2)$ satisfying (20) → `admissible a K` with $A$ the absolute numerator and $D$ the denominator of the reduced rational $a$; reason: the reduced form of a rational number
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Lemma A.2, p.36 (PDF p.38); standing assumptions of App. A, p.36

import Mathlib
import Definitions.Def_HZTractability_kappa
import Definitions.Def_HZTractability_admissible
import Definitions.Def_HZTractability_Lp
import Definitions.Def_HZTractability_bvQ

namespace HZTractability

/-- **Lemma A.2 (Supply and population inequalities)** (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, p.36 (PDF 38)), under the standing assumptions of
Appendix A (p.36; as in Lemma A.1): at each vertex, with degree pair `(h_v, o_v)`,

1. (29): `o_vK < S_L < o_vK + b_v` and `(o_vK + b_v)/S_L < aL`;
2. `c_v > b + 1`, `aL S_M > c_v + 10`, and `3(b + 1)(1 + a)/K < 1`;
3. `L S_H > 10` and `(L + η)S_H < c_v`;
4. in particular `c_v > b_v` and `aL S_M > b_v`.

**Formalization Note** `h`, `o` are `h_v`, `o_v`; the counts are the rational formulas of (17). -/
theorem lemma_A_2 (a : ℚ) (ha0 : 0 < a) (ha1 : a < 1) (τ : ℚ) (hτ0 : 0 < τ)
    (hτ1 : τ ≤ kappa / 100) (K : ℕ) (hK : admissible a K) (h o : ℕ) (hh : h ≤ 2)
    (ho1 : 1 ≤ o) (ho2 : o ≤ 2) :
    (o : ℚ) * K < SLQ a K o ∧ SLQ a K o < (o : ℚ) * K + bvQ a h ∧
    ((o : ℚ) * K + bvQ a h) / SLQ a K o < a * Lp a K ∧
    (bb a : ℚ) + 1 < cvQ a K o ∧ cvQ a K o + 10 < a * Lp a K * SMQ a K o ∧
    3 * ((bb a : ℚ) + 1) * (1 + a) / K < 1 ∧
    10 < Lp a K * SHQ a ∧ (Lp a K + eta a τ K) * SHQ a < cvQ a K o ∧
    bvQ a h < cvQ a K o ∧ bvQ a h < a * Lp a K * SMQ a K o := by sorry

end HZTractability
