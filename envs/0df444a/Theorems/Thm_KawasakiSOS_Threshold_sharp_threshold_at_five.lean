-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_sharp_threshold_at_five
-- name    : KawasakiSOS.Threshold.sharp_threshold_at_five
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:06:55.7051+00:00
-- url     : https://prove2.me/theorems/e7946823-6924-4b25-a437-b4d3a9ea1468
-- title:
--   Theorem 1.1: sharp threshold at $k=5$
-- statement:
--   Fix $\lambda>1$, and let $\tau(\varepsilon)$ be the mixing time of the lazy Kawasaki dynamics on the cycle $C_k$ with total mass $n$.
--
--   1. If $k\in\{2,3,4\}$, then $\tau(1/4)=\exp(\Theta(n))$: there are constants $c,C>0$ and $N$, depending only on $\lambda$, such that for all $n\ge N$ with $n\ge k$,
--
--   $$e^{cn}\le\tau(1/4)\le e^{Cn}.$$
--
--   2. If $5\le k\le n$, then $\tau(\varepsilon)$ is polynomial in $n$, $k$ and $\log(1/\varepsilon)$: there are constants $C>0$ and $a\in\mathbb N$, depending only on $\lambda$, such that for all $5\le k\le n$ and all $\varepsilon\in(0,1)$,
--
--   $$\tau(\varepsilon)\le C\Bigl(nk\bigl(1+\log\tfrac1\varepsilon\bigr)\Bigr)^a.$$
--
--   This is the main result of the source. The mixing behaviour changes at exactly $k=5$, from an energy barrier of order $n$ to polynomial mixing in $n$ and $k$ together.
--
--   Differences from the source:
--   - reading: "τ(1/4) = exp(Θ(n)), where the constants may depend on λ" → ∃ c C > 0 and N, depending on λ only, with exp(c n) ≤ τ(1/4) ≤ exp(C n) for all n ≥ N, n ≥ k; reason: Θ is an asymptotic statement in n; the three values of k share constants, which is equivalent since there are finitely many
--   - reading: "polynomial in n, k, and log(1/ε) for every fixed λ" → ∃ C > 0, a ∈ ℕ depending on λ only, with τ(ε) ≤ C (n k (1 + log(1/ε)))^a for all 5 ≤ k ≤ n and ε in (0,1); reason: every polynomial in the three quantities is bounded this way since n, k ≥ 1, and conversely; the range of ε is that of Theorem 1.2, and the 1 + keeps the base positive as ε → 1
--   - encoding: τ(ε) is the least t with d(t) ≤ ε → a conjunct also asserts that {t | d(t) ≤ ε} is nonempty; reason: Lean's sInf on ℕ is 0 on the empty set, so without the conjunct an upper bound could hold for free
--   - reading: "its mixing time" → the worst-case total variation mixing time of the lazy chain; reason: the source does not define the term; this is the standard meaning, as in its reference [LPW17]
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Theorem 1.1, p. 1 (PDF p. 2)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_tau
import Definitions.Def_KawasakiSOS_Threshold_mixingSet

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Theorem 1.1, p. 1 (PDF p. 2).

Formalization Notes:
- reading: "τ(1/4) = exp(Θ(n)), where the constants may depend on λ" → ∃ c C > 0 and N, depending on λ only, with exp(c n) ≤ τ(1/4) ≤ exp(C n) for all n ≥ N, n ≥ k. Θ is an asymptotic statement in n; the three values of k share constants, which is equivalent since there are finitely many.
- reading: "polynomial in n, k, and log(1/ε) for every fixed λ" → ∃ C > 0, a ∈ ℕ depending on λ only, with τ(ε) ≤ C (n k (1 + log(1/ε)))^a for all 5 ≤ k ≤ n and ε in (0,1). Every polynomial in the three quantities is bounded this way since n, k ≥ 1, and conversely; the range of ε is that of Theorem 1.2, and the 1 + keeps the base positive as ε → 1.
- encoding: τ(ε) is the least t with d(t) ≤ ε → a conjunct also asserts that {t | d(t) ≤ ε} is nonempty. Lean's sInf on ℕ is 0 on the empty set, so without the conjunct an upper bound could hold for free.
- reading: "its mixing time" → the worst-case total variation mixing time of the lazy chain. The source does not define the term; this is the standard meaning, as in its reference [LPW17]. -/
theorem sharp_threshold_at_five (lam : ℝ) (hlam : 1 < lam) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ (k n : ℕ) [NeZero k], (k = 2 ∨ k = 3 ∨ k = 4) → k ≤ n → N ≤ n →
      (mixingSet n k lam (1 / 4)).Nonempty ∧
        Real.exp (c * (n : ℝ)) ≤ (tau n k lam (1 / 4) : ℝ) ∧
        (tau n k lam (1 / 4) : ℝ) ≤ Real.exp (C * (n : ℝ))) ∧
    (∃ (C : ℝ) (a : ℕ), 0 < C ∧ ∀ (k n : ℕ) [NeZero k], 5 ≤ k → k ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
      (mixingSet n k lam ε).Nonempty ∧
        (tau n k lam ε : ℝ) ≤ C * ((n : ℝ) * (k : ℝ) * (1 + Real.log (1 / ε))) ^ a) := by sorry

end KawasakiSOS.Threshold
