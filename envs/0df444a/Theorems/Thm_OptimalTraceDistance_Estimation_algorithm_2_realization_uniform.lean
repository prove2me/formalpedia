-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_algorithm_2_realization_uniform
-- name    : OptimalTraceDistance.Estimation.algorithm_2_realization_uniform
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-23T00:26:22.872674+00:00
-- url     : https://prove2.me/theorems/14218084-b965-4a9f-ad7a-89143fdf3a86
-- title:
--   Realization of Algorithm 2 for all constants
-- statement:
--   Fix any fresh-batch multiplier $C>0$ and any dimension threshold $d_0\ge2$. For every dimension $d\ge2$ and accuracy $0<\varepsilon\le1/32$, there is a single state-independent POVM, acting on $N$ copies of each of the two unknown inputs, whose Born outcome law equals the computed event weights of Algorithm 2 with these parameters. Here
--   $$N=\begin{cases}\lceil C_0d^2/\varepsilon^2\rceil,&d<d_0,\\[2pt] \lceil C_0d\log^2d\rceil+\lceil C\,R(d,\varepsilon)\rceil,&d\ge d_0,\end{cases}\qquad C_0=2^{40},$$
--   and the equality holds for every pair of density matrices $\rho,\sigma$ and every Borel set of reports.
--
--   - For $d<d_0$ the weights are those of measuring each input with Keyl's tomography POVM and reporting $\tfrac12\|\hat\rho-\hat\sigma\|_1$.
--   - For $d\ge d_0$, the first batch performs Keyl tomography of $S_+=(\rho+\sigma)/2$, using samples obtained by choosing $\rho$ or $\sigma$ uniformly. From the report it forms the projector $Q$ onto the eigenspaces below $1/(2\log d)$. It then measures the spectral decomposition of the observable of the estimator polynomial $f$ on a fresh batch drawn from the labelled state, and clips the outcome to $[0,1]$.
--
--   This is the realization obligation of the source's Algorithm 2, stated uniformly in the constants $C$ and $d_0$. The physical construction does not depend on them. The uniform form is what allows the realization to be combined with the variance bound of Proposition 3.2, whose constants are fixed separately.
--
--   **Formalization Note** The statement is identical to `algorithm_2_realization` except that $C$ and $d_0$ are universally quantified instead of existentially quantified. The cost and the weights are the platform definitions `algorithmCost` and `algorithm2Weight`.
-- source:
--   Chen–Gao–Wang, Optimal Trace Distance Estimation, STOC 2027 submission #875, Algorithm 2 (p.11) and §5 (p.21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/875.pdf. Uniform-constant form of the platform theorem algorithm_2_realization.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem algorithm_2_realization_uniform : ∀ C : ℝ, 0 < C → ∀ d₀ : ℕ, 2 ≤ d₀ →
    ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/32 →
      ∃ M : TwoStateMeasurement d (algorithmCost C d₀ d ε),
        ∀ (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ),
          ∀ B : Set ℝ, MeasurableSet B → outcomeLaw M ρ σ hρ hσ B =
            algorithm2Weight C d₀ ε ρ σ hρ hσ B := by sorry

end OptimalTraceDistance.Estimation
