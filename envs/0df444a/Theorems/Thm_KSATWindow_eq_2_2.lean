-- Prove2me | Theorems.Thm_KSATWindow_eq_2_2
-- name    : KSATWindow.eq_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:32.482079+00:00
-- url     : https://prove2.me/theorems/1981a84c-c6f6-4520-a42b-ebb6275c2784
-- title:
--   (2.2) — first-moment tails $\mathbb P(T_n>m)\le 2^n(1-2^{-k})^m$ and $s_n(t)\le\min\{1,2^ne^{-t/2^k}\}$; finite moments
-- statement:
--   Fix $k\ge3$ and $n\ge k$, and let $T_n$ be the first unsatisfiable clause count of random $k$-SAT on $n$ variables. Every fixed assignment survives a uniform signed $k$-clause with probability $1-2^{-k}$, and a union bound over the $2^n$ assignments gives, for every $m\ge0$ and $t\ge0$,
--   $$\mathbb P(T_n>m)\le 2^n(1-2^{-k})^m,\qquad s_n(t)\le\min\{1,\,2^ne^{-t/2^k}\},$$
--   where $s_n(t)$ is the probability that the Poisson-time formula $F_n(t)$ is still satisfiable. In particular the hitting times have finite moments:
--
--   1. $\mathbb E\,T_n^p<\infty$ for every $p\in\mathbb N$;
--   2. $\int_0^\infty t^p\,s_n(t)\,dt<\infty$ for every $p\in\mathbb N$, i.e. every moment of the Poisson-time hitting time $\tau_n$ is finite.
--
--   These tails control the large-time part of every occupation integral in the paper, and the second moment is what Chebyshev's inequality needs.
--
--   Differences from the source:
--   - encoding: n ≥ k (and k ≥ 3, the standing assumption of §2) → hypotheses k ≤ n; reason: for n < k the set of clauses is empty and the clause law is not a probability measure; the paper's n → ∞ leaves small n unspecified
--   - encoding: E f(Fₙ(t)) for the Poisson-time formula Fₙ(t) = F_{n,Π_t} → the Poisson mixture Σ_m e^{−t}t^m/m!·E f(F_{n,m}) in [0,∞]; reason: this is what independence of Π_t and the clauses gives; every statement uses one time t only
--   - encoding: the hitting times have finite moments → MemLp Tₙ p for every p ∈ ℕ, and ∫₀^∞ t^p sₙ(t) dt < ∞ for every p ∈ ℕ; reason: τₙ is not built as a random variable; E τₙ^{p+1} = (p+1)∫₀^∞ t^p sₙ(t) dt, so the second clause is the moment statement for τₙ
--   - encoding: Tₙ → H, the published first-failure count read through ℕ∞ → ℕ; reason: H = Tₙ almost surely for k ≤ n (OAI.RandomKSAT.firstFailure_finite_ae)
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §2, p.5, eq. (2.2)

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_KSATWindow_Window
import Definitions.Def_KSATWindow_Forcing
import Definitions.Def_KSATWindow_PoissonTime
open MeasureTheory ProbabilityTheory OAI.RandomKSAT
open scoped Classical ENNReal

namespace KSATWindow

/-- **(2.2), p.5 — first-moment tails.** G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), §2, p.5.

Fix `k ≥ 3` and `n ≥ k`. For every `m`, `P(Tₙ > m) ≤ 2ⁿ(1 − 2^{−k})^m`, and for every `t ≥ 0`,
`sₙ(t) ≤ min{1, 2ⁿ e^{−t/2^k}}`. "In particular, the hitting times have finite moments": every
moment of `Tₙ` is finite, and every moment of the Poisson-time hitting time `τₙ` is finite, i.e.
`∫₀^∞ t^p sₙ(t) dt < ∞` for every `p` (`E τₙ^{p+1} = (p+1)∫₀^∞ t^p sₙ(t) dt`).

**Formalization Note.** `Tₙ` is `H`; `sₙ(t)` is the Poisson mixture `survivalTime`. -/
theorem eq_2_2 (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) :
    (∀ m : ℕ, (streamLaw n k).real {ω | (m : ℝ) < H ω} ≤
      (2 : ℝ) ^ n * (1 - ((2 : ℝ) ^ k)⁻¹) ^ m) ∧
    (∀ t : ℝ, 0 ≤ t →
      survivalTime n k t ≤ ENNReal.ofReal (min 1 ((2 : ℝ) ^ n * Real.exp (-t / (2 : ℝ) ^ k)))) ∧
    (∀ p : ℕ, MemLp (H : Stream n k → ℝ) (p : ℝ≥0∞) (streamLaw n k)) ∧
    (∀ p : ℕ, ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ p) * survivalTime n k t < ⊤) := by sorry

end KSATWindow
