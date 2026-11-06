-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_low_energy_congestion
-- name    : KawasakiSOS.Threshold.low_energy_congestion
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:05:36.049952+00:00
-- url     : https://prove2.me/theorems/5a9b812b-6b35-42af-9eb0-0f4938e0053e
-- title:
--   Corollary 4.2: congestion of the low-energy paths
-- statement:
--   There is an absolute constant $C>0$ such that for all $\lambda>1$ and $5\le k\le n$ there is a path system of the Kawasaki chain whose paths have the energy property of Proposition 4.1 and satisfy
--
--   $$\rho\le4k\lambda^4(n+1)^{k-1},\qquad\ell\le Cnk.$$
--
--   The bound is polynomial in $n$ for fixed $k$, but exponential in $k$. It settles $k=5$, and for growing $k$ a finer encoding is needed.
--
--   Differences from the source:
--   - reading: "ℓ = O(nk)" → one constant C > 0, quantified before every parameter; reason: the O(·) of the source is read as an absolute constant, uniform in the displayed parameters
--   - reading: "the canonical paths of Proposition 4.1" → there is a path system with the energy property of Proposition 4.1 and the stated ρ and ℓ; reason: Proposition 4.1 is existential, so its paths are named by their properties
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Corollary 4.2, p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_DiaconisStroock_CanonPaths_Eta
import Definitions.Def_DiaconisStroock_Poincare_GraphPaths
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_energy
import Definitions.Def_KawasakiSOS_Threshold_gibbs
import Definitions.Def_KawasakiSOS_Threshold_kawasaki
open DiaconisStroock.Poincare DiaconisStroock.CanonPaths

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Corollary 4.2, p. 10 (PDF p. 11).

Formalization Notes:
- reading: "ℓ = O(nk)" → one constant C > 0, quantified before every parameter. The O(·) of the source is read as an absolute constant, uniform in the displayed parameters.
- reading: "the canonical paths of Proposition 4.1" → there is a path system with the energy property of Proposition 4.1 and the stated ρ and ℓ. Proposition 4.1 is existential, so its paths are named by their properties. -/
theorem low_energy_congestion : ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 1 < lam → ∀ (n k : ℕ) [NeZero k], 5 ≤ k → k ≤ n →
    ∃ γ : Config n k → Config n k → List (Config n k),
      IsWalkSystem (kawasaki n k lam) (gibbs n k lam) γ ∧
      (∀ x y, x ≠ y → ∀ z ∈ γ x y, energy z.1 ≤ max (energy x.1) (energy y.1) + 2) ∧
      eta (kawasaki n k lam) (gibbs n k lam) γ ≤ 4 * (k : ℝ) * lam ^ 4 * ((n : ℝ) + 1) ^ (k - 1) ∧
      (maxPathEdges γ : ℝ) ≤ C * (n : ℝ) * (k : ℝ) := by sorry

end KawasakiSOS.Threshold
