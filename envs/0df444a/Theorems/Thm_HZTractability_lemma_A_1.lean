-- Prove2me | Theorems.Thm_HZTractability_lemma_A_1
-- name    : HZTractability.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:15:52.649445+00:00
-- url     : https://prove2.me/theorems/b6b185a7-074c-4842-a645-66f34d903f83
-- title:
--   Lemma A.1 — parameter feasibility
-- statement:
--   Fix a rational $a\in(0,1)$ written $a=A/D$ in lowest terms, $C=16D^2$, $b=4C$, a rational $\tau$ with $0<\tau\le\kappa/100$ ($\kappa=1/200$), and an admissible $K$ (display (20)). For each of the six degree pairs $h_v\in\{0,1,2\}$, $o_v\in\{1,2\}$:
--
--   1. All supplies and buyer counts $b_v$, $c_v$, $F_v$, $A^R_{Fv}$, $A^R_{Uv}$, $S_L$, $S_M$, $S_H$, $S^R_{Fv}$, $S^R_{Uv}$ of (17), (7), (5) are positive integers.
--   2. $1<L<U$, and
--   $$
--   F_v>S_L+S_M,\qquad c_v>S_H,\qquad A^R_{Fv}>S^R_{Fv},\qquad A^R_{Uv}>S^R_{Uv}.
--   $$
--   3. $aL\ge\dfrac{1+a}{2a}$, $a(U+\eta)<\dfrac1a$, $L+\eta<U$; consequently $a(L+\eta)<1/a$ and $a^2(U+\eta)<1$.
--   4. The decoding error obeys (28):
--   $$
--   \frac{6a^2w(1+\tau)}{L-1}+2\tau<\frac{\kappa}{10},\qquad \frac{\eta}{w}=\tau<\frac{\kappa}{4}.
--   $$
--
--   These are the arithmetic facts that make the market well defined and the exact and approximate analyses go through.
--
--   Differences from the source:
--   - encoding: “all supplies and buyer counts are positive integers” → each rational formula $q$ of (17), (7), (5) satisfies $\lceil q\rceil_+=q$ and $q>0$; reason: the market is built from the natural numbers $\lceil q\rceil_+$; this ties each formula to its count
--   - encoding: $a=A/D$ in lowest terms and $K$ a positive multiple of $D^2(D^2-A^2)$ satisfying (20) → `admissible a K` with $A$ the absolute numerator and $D$ the denominator of the reduced rational $a$; reason: the reduced form of a rational number
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Lemma A.1, p.36 (PDF p.38); standing assumptions of App. A, p.36

import Mathlib
import Definitions.Def_HZTractability_kappa
import Definitions.Def_HZTractability_admissible
import Definitions.Def_HZTractability_Lp
import Definitions.Def_HZTractability_bvQ
import Definitions.Def_HZTractability_FvQ
import Definitions.Def_HZTractability_SRFQ

namespace HZTractability

/-- **Lemma A.1 (Parameter feasibility)** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848, held
version, sha256 74b7bf9f…, p.36 (PDF 38)), under the standing assumptions of Appendix A (p.36): "Fix
a = A/D in lowest terms, C = 16D², b = 4C, and 0 < τ ≤ κ/100. Let K be a positive multiple of
D²(D² − A²) satisfying (20). Every bound below holds for all six degree pairs h_v ∈ {0, 1, 2} and
o_v ∈ {1, 2}."

1. All supplies and buyer counts are positive integers: each of the rational formulas `b_v`, `c_v`,
   `F_v`, `A^R_{Fv}`, `A^R_{Uv}`, `S_L`, `S_M`, `S_H`, `S^R_{Fv}`, `S^R_{Uv}` of (17), (7), (5) is
   positive and equals its natural-number ceiling.
2. `1 < L < U`, `F_v > S_L + S_M`, `c_v > S_H`, `A^R_{Fv} > S^R_{Fv}`, `A^R_{Uv} > S^R_{Uv}`.
3. `aL ≥ (1 + a)/(2a)`, `a(U + η) < 1/a`, `L + η < U`; consequently `a(L + η) < 1/a` and
   `a²(U + η) < 1`.
4. (28): `6a²w(1 + τ)/(L − 1) + 2τ < κ/10` and `η/w = τ < κ/4`.

**Formalization Note** `h`, `o` are the degree pair `(h_v, o_v)`; `κ = 1/200`. "Positive integer"
is stated as `⌈q⌉₊ = q` and `0 < q` for the rational formula `q`, which ties each formula to the
natural-number count used to build the market. -/
theorem lemma_A_1 (a : ℚ) (ha0 : 0 < a) (ha1 : a < 1) (τ : ℚ) (hτ0 : 0 < τ)
    (hτ1 : τ ≤ kappa / 100) (K : ℕ) (hK : admissible a K) (h o : ℕ) (hh : h ≤ 2)
    (ho1 : 1 ≤ o) (ho2 : o ≤ 2) :
    (∀ q ∈ ({bvQ a h, cvQ a K o, FvQ a K o, ARFQ a τ K o, ARUQ a τ K o, SLQ a K o, SMQ a K o,
        SHQ a, SRFQ a τ K o, SRUQ a τ K o} : Set ℚ), ((⌈q⌉₊ : ℕ) : ℚ) = q ∧ 0 < q) ∧
    1 < Lp a K ∧ Lp a K < Up a K ∧
    SLQ a K o + SMQ a K o < FvQ a K o ∧ SHQ a < cvQ a K o ∧
    SRFQ a τ K o < ARFQ a τ K o ∧ SRUQ a τ K o < ARUQ a τ K o ∧
    (1 + a) / (2 * a) ≤ a * Lp a K ∧ a * (Up a K + eta a τ K) < 1 / a ∧
    Lp a K + eta a τ K < Up a K ∧
    a * (Lp a K + eta a τ K) < 1 / a ∧ a ^ 2 * (Up a K + eta a τ K) < 1 ∧
    6 * a ^ 2 * wp a K * (1 + τ) / (Lp a K - 1) + 2 * τ < kappa / 10 ∧
    eta a τ K / wp a K = τ ∧ τ < kappa / 4 := by sorry

end HZTractability
