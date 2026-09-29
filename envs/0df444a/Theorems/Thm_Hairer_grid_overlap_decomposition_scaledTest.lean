-- Prove2me | Theorems.Thm_Hairer_grid_overlap_decomposition_scaledTest
-- name    : Hairer.grid_overlap_decomposition_scaledTest
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T20:07:35.172733+00:00
-- url     : https://prove2.me/theorems/15ff055b-4117-4155-b462-a0ce612e5af1
-- title:
--   Uniform normalized test representation of grid overlaps
-- statement:
--   Let $s=(s_1,\ldots,s_d)$ be a tuple of nonnegative integer weights, $Q=\sum_i s_i$, and $r\ge0$ a derivative order. Write $W(z)=\prod_i\chi(z_i)$, where $\chi(t)=\sigma(t+1)-\sigma(t)$ and $\sigma$ is the smooth transition from zero to one. Fix a smooth compactly supported test function $\varphi$.
--
--   There is a constant $C>0$ such that, for every $0<\delta\le1$, every tuple of coarse widths $c_i\ge\delta^{s_i}$, and every pair of integer grid indices $j,k$, there is a normalized test $\eta\in B^r_{s,0}$ satisfying
--   $$W\bigl((y_i/\delta^{s_i}-j_i)_i\bigr)\,W\bigl((y_i/c_i-k_i)_i\bigr)\,\varphi(y)=C\delta^Q(S^\delta_{s,x}\eta)(y),\qquad x_i=\delta^{s_i}j_i.$$
--   The constant is independent of the scales and grid indices. This gives the normalized test representation needed to estimate individual overlaps when comparing local reconstruction approximations. It does not assert summability of their total contribution or existence of a reconstruction.
-- source:
--   Auxiliary lemma for the smooth partition approach to Hairer reconstruction. Uses the tensor-product smooth bump from the accepted test-function decomposition.

import Definitions.Def_Hairer_TestFunctions

set_option autoImplicit false
noncomputable section

namespace Hairer

theorem grid_overlap_decomposition_scaledTest {d : ℕ} (s : Fin d → ℕ) (r : ℕ)
    {φ : Pt d → ℝ} (hφ : φ ∈ testFunctions d) :
    let W : Pt d → ℝ := fun z ↦ ∏ i,
      (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i))
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (c : Fin d → ℝ), (∀ i, δ ^ s i ≤ c i) →
      ∀ (j k : Fin d → ℤ), ∃ η : Pt d → ℝ, IsTestBall s r η ∧
        ∀ y : Pt d,
          W (fun i ↦ y i / δ ^ s i - (j i : ℝ)) *
            W (fun i ↦ y i / c i - (k i : ℝ)) * φ y =
          (C * δ ^ (scaleDim s : ℝ)) *
            scaledTest s δ (fun i ↦ δ ^ s i * (j i : ℝ)) η y := by sorry

end Hairer
