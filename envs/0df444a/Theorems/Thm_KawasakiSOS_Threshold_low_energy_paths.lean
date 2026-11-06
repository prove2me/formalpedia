-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_low_energy_paths
-- name    : KawasakiSOS.Threshold.low_energy_paths
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:02:53.873612+00:00
-- url     : https://prove2.me/theorems/854b4538-5732-4371-a040-83c07853460e
-- title:
--   Proposition 4.1: paths of low energy
-- statement:
--   There is an absolute constant $C>0$ such that for all $5\le k\le n$ and every pair $x,y\in\Omega_{n,k}$ there is a path of single moves from $x$ to $y$, of length at most $Cnk$, on which every state $z$ satisfies
--
--   $$M(z)\le\max\{M(x),M(y)\}+2.$$
--
--   So from $k=5$ on there is no energy barrier between any two states. This is what fails for $k\le4$.
--
--   Differences from the source:
--   - reading: "length O(nk)" → one constant C > 0, quantified before every parameter; reason: the O(·) of the source is read as an absolute constant, uniform in the displayed parameters
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Proposition 4.1, p. 9 (PDF p. 10)

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Paths
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_energy
import Definitions.Def_KawasakiSOS_Threshold_IsMove
open MarkovMixing DiaconisStroock.Poincare

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Proposition 4.1, p. 9 (PDF p. 10).

Formalization Notes:
- reading: "length O(nk)" → one constant C > 0, quantified before every parameter. The O(·) of the source is read as an absolute constant, uniform in the displayed parameters. -/
theorem low_energy_paths : ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) [NeZero k], 5 ≤ k → k ≤ n → ∀ x y : Config n k,
    ∃ l : List (Config n k), l.head? = some x ∧ l.getLast? = some y ∧ l.IsChain IsMove ∧
      ((pathEdges l).length : ℝ) ≤ C * (n : ℝ) * (k : ℝ) ∧
      ∀ z ∈ l, energy z.1 ≤ max (energy x.1) (energy y.1) + 2 := by sorry

end KawasakiSOS.Threshold
