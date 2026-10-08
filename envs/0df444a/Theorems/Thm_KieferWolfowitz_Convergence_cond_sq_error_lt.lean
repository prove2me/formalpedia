-- Prove2me | Theorems.Thm_KieferWolfowitz_Convergence_cond_sq_error_lt
-- name    : KieferWolfowitz.Convergence.cond_sq_error_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:49:09.833316+00:00
-- url     : https://prove2.me/theorems/adc5805b-9ef9-41dd-b249-ec2792068deb
-- title:
--   (3.28), p. 466 — $E\{(z_n-\theta)^2\mid z_{N_0}=z\}<(z-\theta)^2+s$ for $n>N_0$
-- statement:
--   Assume (2.2) with constant $S$; $M$ strictly increasing for $x<\theta$ and strictly decreasing for $x>\theta$; Condition 1 with constants $\beta,B>0$ and Condition 2 with constants $\rho,R>0$; $a_n,c_n>0$ with $\sum a_nc_n<\infty$ and $\sum a_n^2c_n^{-2}<\infty$; and a Kiefer–Wolfowitz process $(z_n,y_{2n-1},y_{2n})$ with filtration $(\mathcal F_n)$. Let $s>0$ and let $N_0$ satisfy
--   $$c_n<\min\Big(\frac\rho2,\frac\beta2\Big)\ \ (n\ge N_0),\qquad \sum_{n=N_0}^\infty\frac{a_n^2}{c_n^2}<\frac{s}{2R^2+4S},\qquad \sum_{n=N_0}^\infty a_nc_n<\frac{s}{8B}. \tag{3.25–3.27}$$
--   Then for every $n>N_0$, $(z_n-\theta)^2$ is integrable and
--   $$E\{(z_n-\theta)^2\mid\mathcal F_{N_0}\}<(z_{N_0}-\theta)^2+s\quad\text{almost surely}.$$
--
--   This is the paper's (3.28), $E\{(z_n-\theta)^2\mid z_{N_0}=z\}<(z-\theta)^2+s$: once the step sizes are small, the iterates cannot drift far, in mean square, from where they are at time $N_0$. With Chebyshev's inequality and the subsequence of (3.19)–(3.24) it closes the proof.
--
--   **Formalization Note** The paper conditions on the event $z_{N_0}=z$; the statement conditions on the past $\mathcal F_{N_0}$, which contains $\sigma(z_{N_0})$, and gives the bound almost surely with $z=z_{N_0}$. The tail sums are written $\sum_{n\ge0}a_{N_0+n}^2/c_{N_0+n}^2$ and $\sum_{n\ge0}a_{N_0+n}c_{N_0+n}$; the summability hypotheses make them genuine sums rather than Lean's default value $0$. Integrability of $(z_n-\theta)^2$ is part of the conclusion. Lean indices are 0-based throughout (Lean $N_0$ is the paper's $N_0+1$).
-- source:
--   Kiefer & Wolfowitz, Stochastic estimation of the maximum of a regression function, Ann. Math. Statist. 23 (1952), p. 465, (3.25); p. 466, (3.26)–(3.28)

import Mathlib
import Definitions.Def_KieferWolfowitz_Convergence_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace KieferWolfowitz.Convergence

/-- Kiefer & Wolfowitz (1952), (3.28), p. 466: if `N₀` satisfies (3.25)–(3.27) for `s > 0`, then for
every `n > N₀`, `E{(z_n − θ)² | z_{N₀}} < (z_{N₀} − θ)² + s` almost surely, where the conditioning
is on the past `ℱ N₀` (which contains `σ(z_{N₀})`), and `(z_n − θ)²` is integrable. -/
theorem cond_sq_error_lt {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (S θ : ℝ)
    (hS : SecondMomentBound H S) (hM : Unimodal (regFun H) θ)
    (β B : ℝ) (hβ : 0 < β) (hB : 0 < B) (h1 : Cond1 (regFun H) θ β B)
    (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) (h2 : Cond2 (regFun H) ρ R)
    (a c : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hc : ∀ n, 0 < c n)
    (hac : Summable (fun n => a n * c n)) (hac2 : Summable (fun n => a n ^ 2 / c n ^ 2))
    (z₁ : ℝ) (z yminus yplus : ℕ → Ω → ℝ) (hz : IsKWProcess H a c z₁ P ℱ z yminus yplus)
    (s : ℝ) (hs : 0 < s) (N₀ : ℕ)
    (h325 : ∀ n, N₀ ≤ n → c n < min (ρ / 2) (β / 2))
    (h326 : ∑' n, a (N₀ + n) ^ 2 / c (N₀ + n) ^ 2 < s / (2 * R ^ 2 + 4 * S))
    (h327 : ∑' n, a (N₀ + n) * c (N₀ + n) < s / (8 * B))
    (n : ℕ) (hn : N₀ < n) :
    Integrable (fun ω => (z n ω - θ) ^ 2) P ∧
    ∀ᵐ ω ∂P, P[fun ω' => (z n ω' - θ) ^ 2 | ℱ N₀] ω < (z N₀ ω - θ) ^ 2 + s := by sorry

end KieferWolfowitz.Convergence
