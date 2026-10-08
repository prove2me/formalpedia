-- Prove2me | Theorems.Thm_KieferWolfowitz_Convergence_liminf_expect_K_eq_zero
-- name    : KieferWolfowitz.Convergence.liminf_expect_K_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:48:41.25577+00:00
-- url     : https://prove2.me/theorems/d08ca38e-157e-4caa-9acc-523771ba76ee
-- title:
--   (3.18), p. 465 — $\liminf_{n\to\infty}E\{K_n|z_n-\theta|\}=0$
-- statement:
--   Under the same hypotheses as (3.15) — (2.2), unimodality of $M$ about $\theta$, Conditions 1 and 2, step sizes with (2.3)–(2.6), and a Kiefer–Wolfowitz process — let
--   $$K_n=\left|\frac{M(z_n+c_n)-M(z_n-c_n)}{c_n}\right| \tag{3.16}.$$
--   Then each $K_n|z_n-\theta|$ is integrable and
--   $$\liminf_{n\to\infty} E\{K_n\,|z_n-\theta|\}=0 .$$
--
--   This is the step at which the divergence $\sum a_n=\infty$ enters: the iterates come close to $\theta$, in the averaged sense $E\{K_n|z_n-\theta|\}$, along a subsequence.
--
--   **Formalization Note** The sequence $E\{K_n|z_n-\theta|\}$ is nonnegative, so "$\liminf=0$" is stated as: for every $\varepsilon>0$, $E\{K_n|z_n-\theta|\}<\varepsilon$ for infinitely many $n$. This avoids Lean's `liminf` default value on sequences not known to be bounded. Condition 3 is not needed and is omitted. Integrability is part of the conclusion. Lean index $n$ is the paper's $n+1$.
-- source:
--   Kiefer & Wolfowitz, Stochastic estimation of the maximum of a regression function, Ann. Math. Statist. 23 (1952), p. 465, (3.16)–(3.18)

import Mathlib
import Definitions.Def_KieferWolfowitz_Convergence_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace KieferWolfowitz.Convergence

/-- Kiefer & Wolfowitz (1952), (3.18), p. 465: `lim inf_{n→∞} E{K_n |z_n − θ|} = 0`, stated for the
nonnegative sequence `E{K_n |z_n − θ|}` as "for every `ε > 0` it is `< ε` for infinitely many `n`",
together with the integrability of each `K_n |z_n − θ|`. -/
theorem liminf_expect_K_eq_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (S θ : ℝ)
    (hS : SecondMomentBound H S) (hM : Unimodal (regFun H) θ)
    (h1 : ∃ β B : ℝ, 0 < β ∧ 0 < B ∧ Cond1 (regFun H) θ β B)
    (h2 : ∃ ρ R : ℝ, 0 < ρ ∧ 0 < R ∧ Cond2 (regFun H) ρ R)
    (a c : ℕ → ℝ) (hac : StepSizes a c) (z₁ : ℝ)
    (z yminus yplus : ℕ → Ω → ℝ) (hz : IsKWProcess H a c z₁ P ℱ z yminus yplus) :
    (∀ n, Integrable (fun ω => K (regFun H) c z n ω * |z n ω - θ|) P) ∧
    ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, ∫ ω, K (regFun H) c z n ω * |z n ω - θ| ∂P < ε := by sorry

end KieferWolfowitz.Convergence
