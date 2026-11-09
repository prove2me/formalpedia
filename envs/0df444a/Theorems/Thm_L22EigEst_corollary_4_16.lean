-- Prove2me | Theorems.Thm_L22EigEst_corollary_4_16
-- name    : L22EigEst.corollary_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:26:26.614922+00:00
-- url     : https://prove2.me/theorems/af90d746-f55e-4221-a16c-16c4dafbcea3
-- title:
--   Corollary 4.16 — $\mathbb E\|Z\|_2=O(\sigma+\sigma_*\sqrt{\log d})$ for symmetric $Z$ with independent centered entries
-- statement:
--   There is a universal constant $K$ such that the following holds. Let $d\ge2$ and let $Z$ be a random symmetric $d\times d$ real matrix with zero diagonal whose entries $\{Z_{ij}\}_{i<j}$ are independent and centered, $\mathbb E Z_{ij}=0$. Let
--
--   $$\sigma^2=\max_i\sum_j\mathbb E[Z_{ij}^2],\qquad \sigma_*=\max_{i,j}\|Z_{ij}\|_\infty .$$
--
--   Then
--
--   $$\mathbb E\|Z\|_2\le K\big(\sigma+\sigma_*\sqrt{\log d}\big).$$
--
--   This is the expectation form of the Bandeira–van Handel bound [BvH16, Corollary 3.12] for entries that need not be symmetric random variables. Only the entry term $\sigma_*$ carries the $\sqrt{\log d}$ factor, which is what makes the choice $q=1/\sqrt{\log(1/\varepsilon)}$ in Lemma 4.7 work.
--
--   Differences from the source:
--   - encoding: E∥Z∥2 = O(σ + σ∗√log d) → ∃ universal K, ∫ ‖Z‖₂ ≤ K(σ + B√log d); reason: O(·) with one constant chosen before d, the probability space and Z
--   - encoding: σ∗ = max_ij ∥Z_ij∥∞ → any B with |Z_ij| ≤ B almost surely for all i, j; reason: the bound for every a.s. bound B is equivalent to the bound with the least one (the essential supremum, itself an a.s. bound); with no finite bound the printed right side is infinite
--   - encoding: a random matrix with independent entries {Z_ij}_{i<j} → Z : Ω → ℝ^{d×d} on a probability space, entries measurable, iIndepFun over the pairs i < j; reason: Lean's model of random variables; bounded measurable entries make every expectation the integral of an integrable function
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Corollary 4.16, p.23

import Definitions.Def_L22EigEst_subMat
import Definitions.Def_WainwrightHDS_EigPert_opNorm2

open MeasureTheory ProbabilityTheory WainwrightHDS.EigPert

namespace L22EigEst

/-- **Corollary 4.16** (p.23), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "Let Z ∈ ℝ^{d×d}, d ≥ 2, be a symmetric random matrix with zero diagonal and
independent centered entries {Zij}_{i<j}, and let σ² := max_i Σ_j E[Z²ij], σ∗ := max_ij ∥Zij∥∞.
Then E∥Z∥2 = O(σ + σ∗√log d)."

**Formalization Note.** The O(·) is one universal constant `K`, chosen before `d`, the probability
space and `Z`. `Z` is a function on a probability space whose entries are measurable;
"independent entries {Z_ij}_{i<j}" is `iIndepFun` over the pairs `i < j` (`Pair d`). `‖Z_ij‖∞` enters
through an arbitrary almost-sure bound `B` on every entry: the bound for every such `B` is
equivalent to the bound with the least one (the essential supremum), and without a finite bound the
printed right side is infinite. With bounded measurable entries every integral below is of an
integrable function. `log` is natural; `‖·‖₂` is `opNorm2`. -/
theorem corollary_4_16 :
    ∃ K : ℝ, ∀ (d : ℕ), 2 ≤ d → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (Z : Ω → Matrix (Fin d) (Fin d) ℝ) (B : ℝ),
      (∀ i j, Measurable (fun ω => Z ω i j)) →
      (∀ ω, (Z ω).IsHermitian) → (∀ ω i, Z ω i i = 0) →
      iIndepFun (fun (x : Pair d) (ω : Ω) => Z ω x.1.1 x.1.2) μ →
      (∀ i j, ∫ ω, Z ω i j ∂μ = 0) →
      (∀ i j, ∀ᵐ ω ∂μ, |Z ω i j| ≤ B) →
      ∫ ω, opNorm2 (Z ω) ∂μ ≤
        K * (Real.sqrt (⨆ i : Fin d, ∑ j, ∫ ω, Z ω i j ^ 2 ∂μ) +
          B * Real.sqrt (Real.log d)) := by sorry

end L22EigEst
