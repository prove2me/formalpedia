-- Prove2me | Theorems.Thm_MasulloRH_literaturePrimeSum_eq_primePowerTraceSum
-- name    : MasulloRH.literaturePrimeSum_eq_primePowerTraceSum
-- status  : Proved
-- author  : @Calvin Yost-Wolff
-- created : 2026-11-20T23:01:09.56009+00:00
-- url     : https://prove2.me/theorems/3e24de82-0780-49bd-8c22-d9e04f9b8bb3
-- title:
--   Von Mangoldt reindexing for the rational trace formula
-- statement:
--   The prime term in the literature form of Weil’s explicit formula agrees with the rational trace formula’s prime-power term after pulling the test function back along the exponential map. For any test function $\phi:\mathbb R\to\mathbb C$, the formal infinite sums agree:
--
--   $$
--   \sum_{n\geq0}\frac{\Lambda(n)}{\sqrt n}\bigl(\phi(e^{\log n})+\phi(e^{-\log n})\bigr)
--   =\sum_{p\text{ prime}}\sum_{k\geq1}\frac{\log p}{\sqrt{p^k}}\bigl(\phi(p^k)+\phi(p^{-k})\bigr).
--   $$
--
--   The $n=0$ term is zero with Mathlib’s totalized operations. For the mission’s compactly supported tests, only finitely many terms contribute. The right-hand side uses `MasulloRH.primePowerTraceTerm`. Formalized by GPT (Codex).
-- source:
--   Masullo, The Music of the Primes, Theorem 12.5.1.1, pp. 519–520, rational specialization. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf ; literature form in https://github.com/anthropics/formal-math/blob/main/zeta23/Zeta23/ExplicitFormula.lean#L58-L66

import Definitions.Def_MasulloRH_RationalTrace
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open scoped ArithmeticFunction.vonMangoldt

theorem MasulloRH.literaturePrimeSum_eq_primePowerTraceSum (φ : ℝ → ℂ) :
    (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) *
      (φ (Real.exp (Real.log n)) + φ (Real.exp (-Real.log n)))) =
      ∑' i : Nat.Primes × ℕ, MasulloRH.primePowerTraceTerm φ i := by sorry
