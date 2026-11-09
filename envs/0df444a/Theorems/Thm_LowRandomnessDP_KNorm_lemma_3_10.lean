-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_lemma_3_10
-- name    : LowRandomnessDP.KNorm.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:15.685311+00:00
-- url     : https://prove2.me/theorems/25fa8e5f-069e-4677-a770-563fb41450be
-- title:
--   Lemma 3.10 — exact exponential partition tail
-- statement:
--   Let $\varepsilon>0$, $\alpha\ge1$, $M\ge1$, $A>0$, $A'=\max(2A,A+3)$ and $C=2A'+2$. Let $\mathcal P$ be a $(k_d,\rho)$-MSSP with $\rho\ge C\alpha d/\varepsilon$ and $k_d(\ell)\le M e^{A\alpha d/\ell}$. Fix any $v$ and nonnegative real scores $s_P\ge\Delta_P(v)$, with $s_{P_0}=0$ for some cell. Then the full normalizer is finite and at least one, the proportional weights define a mass-one law, and
--
--   $$\Pr[P\notin\mathcal P_{<\gamma}(v)]\le2M e^{(2A+1)\alpha-\alpha d\gamma},\qquad\gamma\ge1/d.$$
--
--   This retains all score choices and the exact tail constant for utility and entropy estimates.
--
--   Differences from the source:
--   - encoding: real vectors and their K-norm → Fin d → ℝ with the Minkowski gauge of the exact compact convex symmetric absorbing disk; reason: coordinate encoding preserves all real vectors and all source norms; compactness excludes nontrivial linear subspaces
--   - encoding: probabilities and nonnegative expectations → ENNReal sums and mass-one PMFs, with finite positive normalizers proved in the conclusion; reason: retains divergent expectations as infinity and prevents divergent real sums from becoming zero
--   - encoding: s_P(·) evaluated at the arbitrary fixed point v → an arbitrary real score vector s on the cells; reason: only its values at v enter the statement; every such vector is realized by functions constant in v
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf, Lemma 3.10, PDF page 14 / printed page 12

import Definitions.Def_LowRandomnessDP_KNorm_Sampling

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace LowRandomnessDP.KNorm

theorem lemma_3_10 {d : ℕ} (K : Set (Vec d)) (hK : IsBody K)
    (P : CellPartition d) (k : ℕ → ℕ) (ρ : ℝ) (hP : IsMSSP K P k ρ)
    (ε α M A : ℝ) (hε : 0 < ε) (hα : 1 ≤ α) (hM : 1 ≤ M) (hA : 0 < A)
    (hscale : (2 * max (2 * A) (A + 3) + 2) * α * d / ε ≤ ρ)
    (hk : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ d →
      (k ℓ : ℝ) ≤ M * Real.exp (A * α * d / ℓ))
    (v : Vec d) (s : P.Cell → ℝ) (hs : ∀ c, 0 ≤ s c)
    (hdom : ∀ c, cellDistance K P c v ≤ s c) (hzero : ∃ c, s c = 0) :
    1 ≤ normalizer ε s ∧ Normalizable ε s ∧
    ∃ p : PMF P.Cell, (∀ c, p c = gibbsMass ε s c) ∧
      ∀ γ : ℝ, 1 / (d : ℝ) ≤ γ →
        eventMass p (nearCells K P ρ γ v)ᶜ ≤
          ENNReal.ofReal (2 * M * Real.exp ((2 * A + 1) * α - α * d * γ)) := by sorry

end LowRandomnessDP.KNorm
