-- Prove2me | Theorems.Thm_KieferWolfowitz_Convergence_sq_diff_le
-- name    : KieferWolfowitz.Convergence.sq_diff_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:48:16.187225+00:00
-- url     : https://prove2.me/theorems/a5996d4a-7211-4299-974f-3a03bc3cfacc
-- title:
--   (3.11)–(3.12), p. 464 — $E\{(y_{2n}-y_{2n-1})^2\mid z_n\}\le 2S+R^2$ when $c_n<\rho/2$
-- statement:
--   Let $H$ be a family of observation laws with regression function $M$, satisfying the variance bound (2.2) with constant $S$ and Condition 2 with constants $\rho,R>0$. Let $(z_n,y_{2n-1},y_{2n})$ be a Kiefer–Wolfowitz process (2.7) with positive $c_n$, on a probability space with filtration $(\mathcal F_n)$. If $c_n<\rho/2$, then $(y_{2n}-y_{2n-1})^2$ is integrable and
--   $$E\{(y_{2n}-y_{2n-1})^2\mid \mathcal F_n\}\le 2S+R^2\ \text{ a.s.},\qquad E(y_{2n}-y_{2n-1})^2\le 2S+R^2 .$$
--
--   The paper states these "for large enough $n$", meaning those $n$ with $|2c_n|<\rho$, so that (2.9) gives $[M(z_n+c_n)-M(z_n-c_n)]^2<R^2$ (3.10). The bound controls the noise term $(a_n^2/c_n^2)e_n$ of (3.6); with $\sum a_n^2c_n^{-2}<\infty$ it makes $\sum (a_n^2/c_n^2)e_n$ converge.
--
--   **Formalization Note** "For large enough $n$" is made explicit as the hypothesis $c_n<\rho/2$, the condition the paper itself imposes in (3.25). The paper conditions on $z_n$; the statement conditions on the past $\mathcal F_n$, which contains $z_n$ and with respect to which the conditional law of the pair is given. Integrability is part of the conclusion, so the bounds are not satisfied by Lean's default value $0$ for a non-integrable function. Lean index $n$ is the paper's $n+1$.
-- source:
--   Kiefer & Wolfowitz, Stochastic estimation of the maximum of a regression function, Ann. Math. Statist. 23 (1952), p. 464, (3.10)–(3.12)

import Mathlib
import Definitions.Def_KieferWolfowitz_Convergence_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace KieferWolfowitz.Convergence

/-- Kiefer & Wolfowitz (1952), (3.11)–(3.12), p. 464: whenever `c_n < ρ/2` (the explicit form of
"for large enough n"), `E{(y_{2n} − y_{2n−1})² | z_n} ≤ 2S + R²` and `E(y_{2n} − y_{2n−1})² ≤ 2S + R²`,
the squared difference being integrable. The conditioning is on the past `ℱ n`. -/
theorem sq_diff_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (S : ℝ) (hS : SecondMomentBound H S)
    (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) (h2 : Cond2 (regFun H) ρ R)
    (a c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (z₁ : ℝ)
    (z yminus yplus : ℕ → Ω → ℝ) (hz : IsKWProcess H a c z₁ P ℱ z yminus yplus)
    (n : ℕ) (hcn : c n < ρ / 2) :
    Integrable (fun ω => (yplus n ω - yminus n ω) ^ 2) P ∧
    P[fun ω => (yplus n ω - yminus n ω) ^ 2 | ℱ n] ≤ᵐ[P] (fun _ => 2 * S + R ^ 2) ∧
    ∫ ω, (yplus n ω - yminus n ω) ^ 2 ∂P ≤ 2 * S + R ^ 2 := by sorry

end KieferWolfowitz.Convergence
