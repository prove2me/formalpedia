-- Prove2me | Theorems.Thm_KallMayerSLP_Bonferroni_binomial_moment_two_marginals
-- name    : KallMayerSLP.Bonferroni.binomial_moment_two_marginals
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:36.88146+00:00
-- url     : https://prove2.me/theorems/3eaea97c-f0ba-4034-83c4-1dd3aaf084a5
-- title:
--   $S_2(x)$ from the marginals (corrected: middle term $\mathbb P(B_i\cap B_j)$)
-- statement:
--   For a random vector $\xi:\Omega\to\mathbb R^r$, $r\ge1$, on a probability space and $x\in\mathbb R^r$, for all $i,j$,
--   $$
--   \mathbb P(B_i\cap B_j)=1-\mathbb P(A_i)-\mathbb P(A_j)+\mathbb P(A_i\cap A_j),
--   $$
--   with $\mathbb P(A_i)=F_i(x_i)$ and $\mathbb P(A_i\cap A_j)=F_{ij}(x_i,x_j)$, and
--   $$
--   S_2(x)=\sum_{1\le i<j\le r}\mathbb P(B_i\cap B_j)=\binom{r}{2}-(r-1)\sum_{i=1}^rF_i(x_i)+\sum_{1\le i<j\le r}F_{ij}(x_i,x_j).
--   $$
--   So the second binomial moment needs only the one- and two-dimensional marginal distributions.
--
--   Differences from the source:
--   - encoding: events $B_1,\dots,B_r$ (or variables $v_1,\dots,v_r$) indexed by $1,\dots,r$ → indexed by `Fin r`, that is by $0,\dots,r-1$; reason: Lean convention; same instances
--   - encoding: the number $r$ of events $B_1,\dots,B_r$ (the dimension of $\xi$ with values in $\mathbb R^r$) is left implicit → hypothesis `1 ≤ r`; reason: the family $B_1,\dots,B_r$ starts at $B_1$, so the book has $r\ge1$; the hypothesis excludes only the empty family
--   - correction: the middle term of the display for $S_2(x)$ is $\sum_{i<j}\mathbb P(A_i\cap A_j)$ → the middle term is $\sum_{i<j}\mathbb P(B_i\cap B_j)$; reason: the printed term contradicts (3.10): for $r=2$, $\xi\equiv0$, $x=(1,1)$, one has $\mathbb P(A_1\cap A_2)=1$ but $S_2(x)=\mathbb P(B_1\cap B_2)=0$
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, p.289 (PDF 298)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_lowerEvent
import Definitions.Def_KallMayerSLP_Bonferroni_exceedanceEvent
import Definitions.Def_KallMayerSLP_Bonferroni_marginalCDF
import Definitions.Def_KallMayerSLP_Bonferroni_bivariateCDF

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- `ℙ(B_i ∩ B_j) = 1 - ℙ(A_i) - ℙ(A_j) + ℙ(A_i ∩ A_j)`, `ℙ(A_i) = F_i(x_i)`,
`ℙ(A_i ∩ A_j) = F_ij(x_i, x_j)`, and
`S₂(x) = ∑_{i<j} ℙ(B_i ∩ B_j) = (r choose 2) - (r - 1) ∑_i F_i(x_i) + ∑_{i<j} F_ij(x_i, x_j)`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, §3.4, p.289 (PDF 298).

**Formalization Note.** The book prints `∑_{i<j} ℙ(A_i ∩ A_j)` as the middle term of the display
for `S₂(x)`. By (3.10) the middle term is `∑_{i<j} ℙ(B_i ∩ B_j)`, which is what the right-hand
side of that display equals, and that is what is stated here. The printed middle term is false
for `r = 2`, `ξ ≡ 0`, `x = (1, 1)`: then `ℙ(A₁ ∩ A₂) = 1` but `S₂(x) = ℙ(B₁ ∩ B₂) = 0`. -/
theorem binomial_moment_two_marginals {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (ξ : Ω → Fin r → ℝ) (hξ : Measurable ξ) (x : Fin r → ℝ) :
    (∀ i j, μ.real (exceedanceEvent ξ x i ∩ exceedanceEvent ξ x j) =
      1 - μ.real (lowerEvent ξ x i) - μ.real (lowerEvent ξ x j) +
        μ.real (lowerEvent ξ x i ∩ lowerEvent ξ x j)) ∧
    (∀ i, μ.real (lowerEvent ξ x i) = marginalCDF μ ξ i (x i)) ∧
    (∀ i j, μ.real (lowerEvent ξ x i ∩ lowerEvent ξ x j) = bivariateCDF μ ξ i j (x i) (x j)) ∧
    binomialMoment μ (exceedanceEvent ξ x) 2 =
      ∑ p ∈ Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2),
        μ.real (exceedanceEvent ξ x p.1 ∩ exceedanceEvent ξ x p.2) ∧
    ∑ p ∈ Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2),
        μ.real (exceedanceEvent ξ x p.1 ∩ exceedanceEvent ξ x p.2) =
      (r.choose 2 : ℝ) - ((r : ℝ) - 1) * ∑ i, marginalCDF μ ξ i (x i) +
        ∑ p ∈ Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2),
          bivariateCDF μ ξ p.1 p.2 (x p.1) (x p.2) := by sorry

end KallMayerSLP.Bonferroni
