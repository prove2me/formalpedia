-- Prove2me | Theorems.Thm_IIDMultiItem_TwoPoint_theorem_3_3
-- name    : IIDMultiItem.TwoPoint.theorem_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:59:37.86717+00:00
-- url     : https://prove2.me/theorems/9cfff417-3490-4f0b-8148-e67f7220f18e
-- title:
--   Theorem 3.3 (Theorem A) — the deterministic exclusive-count auction with reserves (3.2) is DSIC, ex-post IR and optimal among all randomized mechanisms; outcome and revenue in polynomial time
-- statement:
--   Let $F=p\delta_a+q\delta_b$ with $0<a<b$, $0<p<1$, $q=1-p$. For all $n,m\ge1$, the auction of §3.2 with the reserves (3.2) (ranking by decreasing exclusive count, ties broken by priority $1<2<\dots<n$) is deterministic, feasible ($x\in[0,1]$, (2.1)), DSIC and ex-post IR (2.2), has nonnegative payments, and its expected revenue is
--   $$\mathrm{OPT}(F;n,m)=mb(1-p^n)+\mathbb E_S\big[c\,[\phi_{c,e^*}]_+\big].\tag{3.6}$$
--   It is optimal among all randomized DSIC, ex-post IR mechanisms: (3.6) is the greatest element of the set of expected revenues of all feasible, DSIC, ex-post IR mechanisms (real allocation probabilities in $[0,1]$, real payments of any sign).
--
--   If $a$, $b$ and $p$ are rational, the outcome of the auction at any profile (the sets $A_i$ and the payments $s_i$) and the value (3.6) can be computed in time polynomial in $n$, $m$ and the bit length of $(a,b,p)$: there is one deterministic bit machine and one polynomial, fixed before all inputs, that on every well-formed instance ($n$ and $m$ in unary, $a,b,p$ as written fractions, and for the outcome a profile as $n$ rows of $m$ bits) halts within the polynomial of the input length with the exact answer, rationals in lowest terms; and likewise for the value.
--
--   This is the paper's headline result for two-point values: it frees both $n$ and $m$ and shows that randomization brings no additional revenue.
--
--   Differences from the source:
--   - encoding: types t ∈ {a, b}^m → types S : Finset (Fin m) (twoPoint a b p m); reason: the identification of Section 3, a bijection preserving values and probabilities
--   - encoding: OPT(F; n, m) = sup of Rev over mechanisms satisfying (2.1) and (2.2), and 'optimal among all randomized DSIC, ex-post IR mechanisms' → IsGreatest (Mechanism.admissibleRevenues (twoPoint a b p m) n) (revFormula a b p n m), together with Rev(auction) = revFormula; reason: the supremum is attained (the paper notes it), so 'OPT = (3.6)' is the statement that (3.6) is the greatest admissible revenue; no junk sSup
--   - encoding: priority order 1 < 2 < ⋯ < n → the order of Fin n, smaller index first; reason: Lean convention (0-based indices)
--   - encoding: computable in time polynomial in n, m and the bit length of (a, b, p) → PolyComputesIn (one BitMachine and one polynomial for all instances) on the codes of OutcomeInput / ValueInput, size = length of the input code (n, m in unary, a, b, p as written fractions, the profile as n·m bits); reason: §1.1 gives n and m in unary and §2.3 measures time in n + m + bit length; the code length is within constant factors of that (plus the n·m bits of a profile)
--   - encoding: the outcome and the value (3.6) as rationals → realRatCode: sign bit, |numerator|, denominator of the reduced rational; reason: an exact output format for a rational; the paper fixes none
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), p. 14 (PDF 16), Theorem 3.3 (= Theorem A, p. 2, PDF 4); proof pp. 15–16 (PDF 17–18) and §B.4

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IIDMultiItem_TwoPoint_Model
import Definitions.Def_IIDMultiItem_TwoPoint_Counts
import Definitions.Def_IIDMultiItem_TwoPoint_Auction
import Definitions.Def_IIDMultiItem_TwoPoint_Computation

open HypergraphUnreliability.FPRAS

namespace IIDMultiItem.TwoPoint

/-- Theorem 3.3 (Theorem A). For all `n, m ≥ 1`, `0 < a < b`, `0 < p < 1`, the auction of §3.2
with the reserves (3.2) is deterministic, feasible, DSIC and ex-post IR, has nonnegative
payments, and its expected revenue is `OPT(F; n, m) = m b (1 − p^n) + E_S[c [ϕ_{c,e*}]_+]` (3.6),
the greatest expected revenue of any (randomized) mechanism satisfying (2.1) and (2.2). For
rational `a, b, p`, one machine computes the outcome of the auction at any profile and one
machine computes the value (3.6), each within a fixed polynomial in the input length (`n`, `m`
in unary). -/
theorem theorem_3_3 :
    (∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → ∀ (a b p : ℝ), 0 < a → a < b → 0 < p → p < 1 →
      (auction a b (reserveStar a b p) : Mechanism (Finset (Fin m)) n m).Deterministic ∧
      (auction a b (reserveStar a b p) : Mechanism (Finset (Fin m)) n m).Feasible ∧
      (auction a b (reserveStar a b p) : Mechanism (Finset (Fin m)) n m).DSIC_IR
        (twoPoint a b p m) ∧
      (∀ (S : Fin n → Finset (Fin m)) (i : Fin n),
        0 ≤ (auction a b (reserveStar a b p) : Mechanism (Finset (Fin m)) n m).s S i) ∧
      (auction a b (reserveStar a b p) : Mechanism (Finset (Fin m)) n m).Rev (twoPoint a b p m) =
        revFormula a b p n m ∧
      IsGreatest (Mechanism.admissibleRevenues (twoPoint a b p m) n) (revFormula a b p n m)) ∧
    PolyComputesIn OutcomeInput.Valid OutcomeInput.encode OutcomeInput.answer
      (fun x => x.encode.length) ∧
    PolyComputesIn ValueInput.Valid ValueInput.encode ValueInput.answer
      (fun x => x.encode.length) := by sorry

end IIDMultiItem.TwoPoint
