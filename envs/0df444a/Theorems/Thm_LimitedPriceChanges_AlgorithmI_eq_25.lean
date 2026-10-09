-- Prove2me | Theorems.Thm_LimitedPriceChanges_AlgorithmI_eq_25
-- name    : LimitedPriceChanges.AlgorithmI.eq_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:37.405786+00:00
-- url     : https://prove2.me/theorems/d57e5093-4022-44de-b758-74af8a762ce1
-- title:
--   (25), p. 25 — the regret from estimation error is at most K₃₃ m T^{1/(m+1)}
-- statement:
--   Consider the censored pricing-inventory model with a scalar parameter under the standing hypotheses of §2–§3 at the true parameter $z$, and run Algorithm-I with valid inputs. The *regret from estimation error*, the second part of the decomposition (23), charges each period $t$ of a stage $i\ge2$ with the optimality gap of its stage's plug-in decision $(\hat p_i,\hat y_i)$.
--
--   There is a constant $K_{33}>0$ such that, for every large enough horizon $T$,
--   $$
--   \sum_{i=2}^{m+1}\ \sum_{t=t_i+1}^{t_{i+1}}\mathbb E\big[G^*(z)-G(\hat p_i,\hat y_i,z)\big]\le K_{33}\,m\,T^{\frac1{m+1}} . \tag{25}
--   $$
--
--   Together with the bounds on the initial-decision, exploration and missed-target parts of (23), this gives the $T^{1/(m+1)}$ rate of Theorem 1.
--
--   **Formalization Note** The page prints the final bound as $K_{17}mT^{1/(m+1)}$, using $I_i/I_{i-1}\le T^{1/(m+1)}$; with the ceilings $I_i=\lceil T^{i/(m+1)}\rceil$ this ratio is only at most $2T^{1/(m+1)}$, so the constant is stated as the existential $K_{33}$ the page names ("for some constant $K_{33}$"). The double sum is the sum over the 0-based Lean periods whose stage is at least $2$; expectations are path-weighted sums in $[0,\infty]$.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 25, (25)

import Mathlib
import Definitions.Def_LimitedPriceChanges_AlgorithmI_Algorithm

namespace LimitedPriceChanges.AlgorithmI

/-- **(25)**, p. 25: the regret from estimation error, the second part of (23). There is a
constant `K₃₃ > 0` such that, for `T` large enough,
`∑_{i=2}^{m+1} ∑_{t = tᵢ+1}^{tᵢ₊₁} 𝔼[G*(z) − G(p̂ᵢ, ŷᵢ, z)] ≤ K₃₃ m T^{1/(m+1)}`.
Here the double sum is the sum over the periods of stages `2, …, m + 1`, each period contributing
the gap of its stage's plug-in decision `(p̂ᵢ, ŷᵢ)`. -/
theorem eq_25 (S : Model) (A : Alg S) (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) :
    ∃ K₃₃ : ℝ, 0 < K₃₃ ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
      A.expect z T (fun d => ∑ s : Fin T,
          if 2 ≤ A.stageOf T s then
            ENNReal.ofReal (S.Gstar A.pstar z -
              S.G (A.phat T (A.stageOf T s) d) (A.yhat T (A.stageOf T s) d) z)
          else 0) ≤
        ENNReal.ofReal (K₃₃ * (A.m : ℝ) * (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1))) := by sorry

end LimitedPriceChanges.AlgorithmI
