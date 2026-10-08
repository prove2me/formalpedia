-- Prove2me | Theorems.Thm_FreedmanTail_Laplace_proposition_3_6
-- name    : FreedmanTail.Laplace.proposition_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:38.542446+00:00
-- url     : https://prove2.me/theorems/bd68f9aa-82dc-4443-9237-5303dbb02be6
-- title:
--   (3.6) Proposition, p. 107 — E{R_λ(T_σ, S_σ)} ≥ 1 for λ ≥ 0 and uniformly bounded stopping times σ, under (1.1)
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space with filtration $\mathcal F_0 \subset \mathcal F_1 \subset \cdots$, and let $X_1, X_2, \dots$ be random variables, $X_n$ being $\mathcal F_n$-measurable, satisfying condition (1.1):
--   $$
--   |X_n| \le 1 \quad\text{and}\quad E\{X_n \mid \mathcal F_{n-1}\} = 0 \qquad (n \ge 1).
--   $$
--   Let $S_n$, $T_n$ and $R_\lambda(v, y) = \exp\{\lambda y - f(\lambda) v\}$ be as in Definition (1.2). Then for any $\lambda \ge 0$ and any stopping time $\sigma$ that is uniformly bounded (there is an integer $N$ with $\sigma \le N$ everywhere),
--   $$
--   E\{R_\lambda(T_\sigma, S_\sigma)\} \ge 1 .
--   $$
--
--   This is the "main inequality" (1.5)(b) of the paper: the process $R_\lambda(T_n, S_n)$ is an expectation-increasing martingale, and optional stopping at bounded times preserves the inequality $E \ge R_\lambda(0,0) = 1$.
--
--   **Formalization Note** Stopping times take values in $\mathbb N \cup \{\infty\}$, as on p. 101; uniform boundedness excludes the value $\infty$, and $S_\sigma$, $T_\sigma$ are read at the finite value of $\sigma$. The conditions $|X_n| \le 1$ and $E\{X_n \mid \mathcal F_{n-1}\} = 0$ are assumed almost surely; together with $\mathcal F_n$-measurability they make every $X_n$ square-integrable, so $V_n$ is a genuine conditional variance. The integrand is bounded, so the Bochner integral is genuine.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 107 (PDF p. 8), (3.6) Proposition; condition (1.1), p. 101

import Mathlib
import Definitions.Def_FreedmanTail_Laplace_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Laplace

/-- Freedman (1975), (3.6) Proposition, p. 107: under condition (1.1)
(`|X_n| ≤ 1` and `E{X_n | ℱ_{n−1}} = 0` for `n ≥ 1`), `E{R_λ(T_σ, S_σ)} ≥ 1` for any `λ ≥ 0`
and any uniformly bounded stopping time `σ`. -/
theorem proposition_3_6 {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hX_bdd : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (hX_mart : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] =ᵐ[P] 0)
    (σ : Ω → WithTop ℕ) (hσ : IsStoppingTime ℱ σ) (hσ_bdd : ∃ N : ℕ, ∀ ω, σ ω ≤ N)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    1 ≤ ∫ ω, R lam (FreedmanTail.Bernstein.T ℱ X P ((σ ω).untopD 0) ω) (FreedmanTail.Bernstein.S X ((σ ω).untopD 0) ω) ∂P := by sorry

end FreedmanTail.Laplace
