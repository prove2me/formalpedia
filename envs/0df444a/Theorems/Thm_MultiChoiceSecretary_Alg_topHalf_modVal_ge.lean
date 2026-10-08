-- Prove2me | Theorems.Thm_MultiChoiceSecretary_Alg_topHalf_modVal_ge
-- name    : MultiChoiceSecretary.Alg.topHalf_modVal_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:27.234512+00:00
-- url     : https://prove2.me/theorems/fbef726b-c228-4374-a401-4ff42334c97d
-- title:
--   Proof sketch of Theorem 2.1, PDF p. 2 — the top ℓ = k/2 elements of Y have expected modified value ≥ (1 − 1/(2√k))·v/2
-- statement:
--   Let $S$ be a finite set of $n$ non-negative reals, $k$ an even integer with $2 \le k \le n$, $\ell = k/2$, $T$ the $k$ largest elements of $S$ and $v$ their sum. Let $Y$ be the set of the first $m$ arrivals of a uniformly random order of $S$, $m \sim B(n,1/2)$ independent, and let $Y_\ell$ be the $\ell$ largest elements of $Y$ (all of $Y$ if $|Y| < \ell$). Then
--
--   $$\mathbb E\big[\mathrm{modval}(Y_\ell)\big] \;\ge\; \Big(1 - \frac{1}{2\sqrt k}\Big)\frac{v}{2},$$
--
--   where the modified value counts only elements of $T$.
--
--   This is the "third consequence" in the proof sketch of Theorem 2.1: it is the benchmark against which the recursive call on the first $m$ arrivals is measured.
--
--   **Formalization Note.** The hypotheses "$k$ even" and $k \le n$ are added. The sketch writes $\ell = k/2$, which is an integer only for even $k$; for odd $k$ with $\ell = \lfloor k/2\rfloor$ the claim fails ($k = 3$, $S$ three nearly equal values: the expectation is about $\tfrac78\cdot\tfrac v3 \approx 0.292\,v$, the bound about $0.356\,v$). For $n < k$ the law of $|Y \cap T|$ changes, as in the binomial claim.
-- source:
--   Kleinberg, A multiple-choice secretary algorithm with applications to online auctions, SODA 2005, PDF p. 2, proof sketch of Theorem 2.1, "Third, the expected modified value of the top ℓ = k/2 elements of Y is bounded below by … ≥ (1 − 1/(2√k)) v/2."

import Mathlib
import Definitions.Def_MultiChoiceSecretary_Alg_Setting

namespace MultiChoiceSecretary.Alg

theorem topHalf_modVal_ge (S : Finset ℝ) (hS : ∀ x ∈ S, 0 ≤ x) (k : ℕ) (hkeven : Even k)
    (h2k : 2 ≤ k) (hkn : k ≤ S.card) :
    (1 - 1 / (2 * Real.sqrt k)) * (topSum S k / 2) ≤
      splitAvg S (fun Y => modVal S k (topK Y (k / 2))) := by sorry

end MultiChoiceSecretary.Alg
