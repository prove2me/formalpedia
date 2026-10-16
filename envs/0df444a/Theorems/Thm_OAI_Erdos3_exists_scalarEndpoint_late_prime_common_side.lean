-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_scalarEndpoint_late_prime_common_side
-- name    : OAI.Erdos3.exists_scalarEndpoint_late_prime_common_side
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:56:50.046006+00:00
-- url     : https://prove2.me/theorems/63728011-e267-4c3b-8d43-cbfec631c155
-- title:
--   Late distinct primes with a common side exist above every scalar endpoint
-- statement:
--   Let $n, E, C, F, a, q$ be natural numbers (`scalarE`, `scalarC`, `scalarF`, `inputPower`, `earlyExponent`) with $n \ge 2$, $E \ge 2$, $C \ge 2$, $F \ge 2$ and $\max(1, q) \le a$. Then there is a natural number $L \ge 2$ (`latePower`) and a natural number $Z \ge 2$ (`sizePower`) such that for every real $p \ge 2$, setting $b = (p+2)^a$, $s = (b+2)^E$, $r =$ `unconditionedCommonSideScalarRatio n` (the natural number $1 + n(\lceil e^{n+2}\rceil + 2)$) and $t = \bigl(8\,(rn + 1)(s+1) + 2\bigr)^C$, we have $p \le t$, $(p+2)^q \le t$, $(s+F)^F \le (p+2)^Z$, and there exist $P : \mathrm{Fin}\,n \to \mathbb N$ with every $P_j$ prime and a natural number $S$ such that: $S =$ `unconditionedCommonSide P` $= 1 + \sum_i P_i$; $S > 0$; $P$ is injective; $P_i \le 2^{n+1} P_j$ for all $i, j$; $e^p \le P_j$ and $P_j \le S$ for all $j$; $e^t \le P_j \le e^{t+n+2}$ for all $j$; $S / P_j \le \exp($`unconditionedCommonSideExtra n`$)$ for all $j$, where `unconditionedCommonSideExtra n` $= \log(1 + n 2^{n+1})$; $e^t \le S \le r e^t$; $S \le \exp((p+2)^L)$; and for every natural number $d$ with $d \le p$,
--   $$\mathrm{unconditionedSpatialWidthCutoff}\bigl(nS,\ \mathrm{unconditionedSpatialTrimFraction}(d, e^{-p}),\ \mathrm{unconditionedCollisionWidth}(P, e^{-p})\bigr) \le \exp((p+2)^Z),$$
--   where `unconditionedSpatialWidthCutoff B τ L` $= \max\bigl(4/\tau,\ 8(1+B)\max(8\lambda, L)/\tau\bigr)$ with $\lambda$ the constant `probabilityProfileLipschitz`, `unconditionedSpatialTrimFraction d σ` $= \sigma/(32(d+1))$, and `unconditionedCollisionWidth P σ` $= 32 \bigl(\prod_j P_j\bigr)^2/\sigma$ (the square of the cardinality of $\prod_j \mathbb Z/P_j$, divided by $\sigma$).
--
--   Lean: `OAI.Erdos3.exists_scalarEndpoint_late_prime_common_side` in `lean/OAI/Combinatorics/Progressions/Lattices/ScalarEndpointLatePrimeCommonSide.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1328` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ScalarEndpointLatePrimeCommonSide.lean#L12

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1328

namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

theorem exists_scalarEndpoint_late_prime_common_side
    (n scalarE scalarC scalarF inputPower earlyExponent : ℕ)
    (hn : 2 ≤ n) (hE : 2 ≤ scalarE) (hC : 2 ≤ scalarC) (_hF : 2 ≤ scalarF)
    (hInput : max 1 earlyExponent ≤ inputPower) :
    ∃ latePower : ℕ, 2 ≤ latePower ∧ ∃ sizePower : ℕ, 2 ≤ sizePower ∧
    ∀ {p : ℝ}, 2 ≤ p →
      let b := (p + 2) ^ inputPower
      let scalarInput := (b + 2) ^ scalarE
      let ratio := unconditionedCommonSideScalarRatio n
      let t := (8 * ((ratio * n : ℕ) + 1 : ℝ) * (scalarInput + 1) + 2) ^ scalarC
      p ≤ t ∧ (p + 2) ^ earlyExponent ≤ t ∧
      (scalarInput + scalarF) ^ scalarF ≤ (p + 2) ^ sizePower ∧
      ∃ (P : Fin n → ℕ) (hprime : ∀ j, (P j).Prime) (S : ℕ),
        S = unconditionedCommonSide P ∧ 0 < S ∧
        Function.Injective P ∧ (∀ i j, P i ≤ 2 ^ (n + 1) * P j) ∧
        (∀ j, Real.exp p ≤ (P j : ℝ) ∧ P j ≤ S) ∧
        (∀ j, Real.exp t ≤ (P j : ℝ) ∧ (P j : ℝ) ≤ Real.exp (t + (n : ℝ) + 2)) ∧
        (∀ j, (S : ℝ) / (P j : ℝ) ≤ Real.exp (unconditionedCommonSideExtra n)) ∧
        Real.exp t ≤ (S : ℝ) ∧ (S : ℝ) ≤ (ratio : ℝ) * Real.exp t ∧
        (S : ℝ) ≤ Real.exp ((p + 2) ^ latePower) ∧
        ∀ nX : ℕ, (nX : ℝ) ≤ p →
          let : ∀ j, NeZero (P j) := fun j => ⟨(hprime j).ne_zero⟩
          unconditionedSpatialWidthCutoff ((n : ℝ) * (S : ℝ))
            (unconditionedSpatialTrimFraction nX (Real.exp (-p)))
            (unconditionedCollisionWidth P (Real.exp (-p))) ≤ Real.exp ((p + 2) ^ sizePower) := by
  sorry

end Erdos3
end
end OAI
