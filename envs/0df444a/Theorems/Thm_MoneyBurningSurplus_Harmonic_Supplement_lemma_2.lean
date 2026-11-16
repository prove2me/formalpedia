-- Prove2me | Theorems.Thm_MoneyBurningSurplus_Harmonic_Supplement_lemma_2
-- name    : MoneyBurningSurplus.Harmonic.Supplement.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:00:43.241897+00:00
-- url     : https://prove2.me/theorems/62be6a51-5044-470a-bd72-bc807a27937a
-- title:
--   Lemma 2 — VCG restricted to a nonempty range S has total utility at least Δ(S) = F(S) − F(S∖{o_S})
-- statement:
--   Let $n\ge2$ agents have nonnegative valuations $v_i:O\to\mathbb R_{\ge0}$ on a nonempty finite outcome set $O$, and write $w(o)=\sum_iv_i(o)$. For $S\subseteq O$ let $F(S)=\max_{o\in S}w(o)$ if $S\neq\emptyset$ and $F(\emptyset)=0$. For a nonempty $S$, let $o_S$ be the tie-broken maximizer of $w$ in $S$ and let VCG restricted to $S$ charge
--
--   $$p_i(S)=\max_{o\in S}\sum_{j\ne i}v_j(o)-\sum_{j\ne i}v_j(o_S).$$
--
--   With the outcome gap $\Delta(S)=F(S)-F(S\setminus\{o_S\})$, for every nonempty $S\subseteq O$,
--
--   $$\sum_{i\in N}\big(v_i(o_S)-p_i(S)\big)\ge\Delta(S).$$
--
--   This is the per-range bound behind the surplus guarantee and the individual rationality of harmonic outcome sampling (Theorem 6).
--
--   **Formalization Note** $F$ is a finite maximum with the value $0$ on the empty set, exactly the paper's convention; the tie-break rule is the same fixed rule as the mechanism's.
--
--   Differences from the source:
--   - encoding: agents N = {1,…,n} with n ≥ 2, nonnegative valuations on a nonempty finite outcome set O → Fin n with 2 ≤ n, real-valued functions O → ℝ with pointwise nonnegativity carried by the domain, Fintype O, Nonempty O, DecidableEq O; reason: relabeling and decidable finite membership change no instance
--   - encoding: a fixed, report-independent tie-breaking rule among maximizing outcomes → a universally quantified tb : Finset O → O with IsTieBreak tb (it returns a member of every nonempty set), applied to the computed maximizer set; reason: the rule receives no reports; every instance of the paper's rule satisfies IsTieBreak
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, Lemma 2, PDF p. 27 (printed p. 26); definitions of F, o_S and Δ, App. D.2, PDF p. 26 (printed p. 25); pivot payment p_i(S_s), App. D.1, PDF p. 26 (printed p. 25)

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Model
import Definitions.Def_MoneyBurningSurplus_Harmonic_Supplement_Range

namespace MoneyBurningSurplus.Harmonic.Supplement

theorem lemma_2
    {n : ℕ} (hn : 2 ≤ n) {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]
    (tb : Finset O → O) (htb : IsTieBreak tb)
    (v : Fin n → O → ℝ) (hv : AGT.IsValProfile valuationDomain v)
    (S : Finset O) (hS : S.Nonempty) :
    outcomeGap tb S v ≤
      ∑ i : Fin n, (v i (rangeVCGOutcome tb S Finset.univ v) -
        rangeVCGPay tb S Finset.univ i v) := by sorry

end MoneyBurningSurplus.Harmonic.Supplement
