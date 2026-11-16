-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_Supplement_lemma_4_10
-- name    : MoneyBurningTrade.IndependentSurplus.Supplement.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:38:36.686134+00:00
-- url     : https://prove2.me/theorems/42a5b86c-253c-453b-b461-c7f72176a171
-- title:
--   Lemma 4.10 — the seller’s expected value under F is at most C
-- statement:
--   Let $n\ge4$, let $q$ be the grid (22) with $\delta=1/(100n)$, $\Delta_i=q_{i+1}-q_{i-1}$ and $C=1/\sum_{r=2}^{n-2}1/\Delta_r$. Let $\tau$ be such that the grid with slack $\tau$ is a separation grid, and let $0<\eta<\min(\tau,\delta^2\min_{2\le i\le n-2}\Delta_i)$. Let $F$ be the correlated law of §4.3: choose $i\in\{2,\dots,n-2\}$ with probability $C/\Delta_i$, then $v_s$ uniform on $[q_{i-1},q_{i-1}+\eta]$ and $v_b$ uniform on $[q_{i+1}-\eta,q_{i+1}]$. Then the seller's value is $F$-integrable and
--
--   $$\mathbb E_{(v_s,v_b)\sim F}[v_s]\le C.$$
--
--   This bounds the term $\mathbb E[v_s]$ in $\mathrm{TU}_M(F)=\mathbb E[v_s]+\mathrm{TS}_M(F)$ for strongly budget-balanced mechanisms in the proof of Theorem 4.2.
--
--   Differences from the source:
--   - encoding: the fixed integer n ≥ 4 of §4.3, chosen with (n − 3)/16 ≥ 1/ε → every natural number n ≥ 4; reason: the lemma does not involve ε and every n ≥ 4 meets the side condition for some ε > 0; the same instances
--   - encoding: E[v_s] → integrability of v_s under F together with the bound on its Bochner integral; reason: v_s is bounded on the support of F; the conclusion rules out the default value 0 and changes no instance
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 4.10; §4.3 "The distribution"; proof in Appendix A.7, printed p. 31 (PDF p. 32); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_CorrelatedLaw

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- Lemma 4.10, §4.3 p.31: under the correlated law `F` of §4.3, for every admissible
`n, τ, η`, the seller's expected value is at most `C`. Integrability of the seller's
value is part of the conclusion. -/
theorem lemma_4_10 (n : ℕ) (τ η : ℝ) (hpar : IsCorrelatedParam n τ η) :
    Integrable (fun p : ℝ × ℝ => p.1) (correlatedLaw n η) ∧
    ∫ p, p.1 ∂(correlatedLaw n η) ≤ corrC n := by sorry

end MoneyBurningTrade.IndependentSurplus.Supplement
