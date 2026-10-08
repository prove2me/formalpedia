-- Prove2me | Theorems.Thm_FreedmanTail_Laplace_proof_4_2_display
-- name    : FreedmanTail.Laplace.proof_4_2_display
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:39.560149+00:00
-- url     : https://prove2.me/theorems/1d183c61-f356-4e6f-8b4e-d650c10c40c4
-- title:
--   Proof of (1.8), (4.2), p. 108 — 1 ≤ E{exp[λS_{τ_a∧n} − f(λ)T_{τ_a∧n}]} ≤ exp[λ(a+1)]·E{exp[−f(λ)T_{τ_a∧n}]}
-- statement:
--   Under condition (1.1) ($X_n$ $\mathcal F_n$-measurable, $|X_n| \le 1$, $E\{X_n \mid \mathcal F_{n-1}\} = 0$ for $n \ge 1$), let $a > 0$, $\lambda > 0$, $f(\lambda) = e^{-\lambda} - 1 + \lambda$, and let $\tau_a$ be the first $n$ with $S_n \ge a$ ($\infty$ if none). Then for every $n \ge 0$,
--   $$
--   1 \le E\{\exp[\lambda S_{\tau_a \wedge n} - f(\lambda) T_{\tau_a \wedge n}]\} \le \exp[\lambda(a+1)] \cdot E\{\exp[-f(\lambda) T_{\tau_a \wedge n}]\} .
--   $$
--
--   Letting $n \to \infty$ in the outer inequality gives Theorem (1.8).
--
--   **Formalization Note** The paper prints the last factor as $\{\exp[-f(\lambda) T_{\tau_a \wedge n}]\}$, without the expectation sign $E$; without it the right side would be a random variable, so the $E$ is restored. $\tau_a \wedge n$ is computed in $\mathbb N \cup \{\infty\}$ and is always finite. Both integrands are bounded, so Bochner integrals are genuine.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 108 (PDF p. 9), (4.2) The proof of (1.8), the display

import Mathlib
import Definitions.Def_FreedmanTail_Laplace_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums
import Definitions.Def_FreedmanTail_Laplace_CrossingTime

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Laplace

/-- Freedman (1975), (4.2), p. 108, the display: under condition (1.1), with `a > 0` and
`λ > 0`, for every `n`, writing `k = τ_a ∧ n`,
`1 ≤ E{exp[λS_k − f(λ)T_k]} ≤ exp[λ(a + 1)] · E{exp[−f(λ)T_k]}`.
(The page omits the `E` of the last factor.) -/
theorem proof_4_2_display {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hX_bdd : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (hX_mart : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] =ᵐ[P] 0)
    (a : ℝ) (ha : 0 < a) (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    1 ≤ ∫ ω, R lam (FreedmanTail.Bernstein.T ℱ X P ((min (tau a X ω) (n : WithTop ℕ)).untopD 0) ω)
        (FreedmanTail.Bernstein.S X ((min (tau a X ω) (n : WithTop ℕ)).untopD 0) ω) ∂P ∧
    ∫ ω, R lam (FreedmanTail.Bernstein.T ℱ X P ((min (tau a X ω) (n : WithTop ℕ)).untopD 0) ω)
        (FreedmanTail.Bernstein.S X ((min (tau a X ω) (n : WithTop ℕ)).untopD 0) ω) ∂P ≤
      Real.exp (lam * (a + 1)) *
        ∫ ω, Real.exp (-(f lam * FreedmanTail.Bernstein.T ℱ X P ((min (tau a X ω) (n : WithTop ℕ)).untopD 0) ω)) ∂P := by sorry

end FreedmanTail.Laplace
