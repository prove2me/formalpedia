-- Prove2me | Theorems.Thm_KhintchineTwoRegime_szarek_equality_case
-- name    : KhintchineTwoRegime.szarek_equality_case
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:40.720001+00:00
-- url     : https://prove2.me/theorems/8d23983a-c233-4432-a6eb-252a7d6532cf
-- title:
--   Equality case of the sharp Khintchine bound: $K_n(\omega)=1/\sqrt2$ iff two coordinates equal $\pm1/\sqrt2$
-- statement:
--   Let $\omega\in\mathbb R^n$ be a unit vector, $\|\omega\|_2=1$. The sharp Khintchine inequality (Szarek) gives $K_n(\omega)\ge1/\sqrt2$. Its equality case is rigid:
--   $$
--   K_n(\omega)=\frac1{\sqrt2}\iff\text{there are } i\ne j \text{ with } |\omega_i|=|\omega_j|=\frac1{\sqrt2}.
--   $$
--   For a unit vector the right-hand side forces every other coordinate to vanish, so up to signs and permutations $\omega=(1/\sqrt2,1/\sqrt2,0,\dots,0)$.
--
--   The paper cites this rigidity and uses it for the uniqueness clauses of Theorems 1 and 2: equality in the tail Khintchine inequality forces precisely two equal nonzero tail coefficients.
--
--   Differences from the source:
--   - encoding: equality is attained only when, up to signs and permutations, ω has two nonzero coordinates, both equal to 1/√2; the best possible value is 1/√2 → K n ω = 1/√2 ↔ ∃ i ≠ j, |ω i| = |ω j| = 1/√2, for every unit vector ω; reason: for a unit vector two coordinates of absolute value 1/√2 force all others to be 0; 'best possible value' is the ← direction
--   - encoding: vectors ω ∈ ℝⁿ with the Euclidean norm ‖·‖₂, coordinates ω₁, …, ωₙ → Fin n → ℝ with the Euclidean norm √(∑ᵢ ωᵢ²) (the published HighDimProb.SparseRecovery.l2Norm), coordinates ω 0, …, ω (n−1); reason: Lean convention (Mathlib's ‖·‖ on Fin n → ℝ is the sup norm); same instances
--   - encoding: E over independent Rademacher signs → uniform average over all sign vectors Fin n → Bool (K); reason: the law of independent Rademacher signs is uniform on {−1, 1}ⁿ; same values
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §1, p.1 (equality case of the sharp Khintchine inequality, [25])

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
open HighDimProb.SparseRecovery (l2Norm)

namespace KhintchineTwoRegime

/-- Equality case of the sharp Khintchine lower bound (Szarek), cited in Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §1, p.1:
after the normalization `‖ω‖₂ = 1` the best possible value of `K_n(ω)` is `1/√2`, attained
only when, up to signs and permutations, `ω` has two nonzero coordinates, both equal to `1/√2`.

**Formalization Note** For a unit vector the right-hand side "two distinct coordinates of
absolute value `1/√2`" forces all other coordinates to vanish. Both directions are stated:
the paper's "best possible value" means the value is attained. -/
theorem szarek_equality_case (n : ℕ) (ω : Fin n → ℝ) (hω : l2Norm ω = 1) :
    K n ω = 1 / Real.sqrt 2 ↔
      ∃ i j : Fin n, i ≠ j ∧ |ω i| = 1 / Real.sqrt 2 ∧ |ω j| = 1 / Real.sqrt 2 := by sorry

end KhintchineTwoRegime
