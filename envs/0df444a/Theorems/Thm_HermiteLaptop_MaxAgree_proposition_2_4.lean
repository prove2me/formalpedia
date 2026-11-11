-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_proposition_2_4
-- name    : HermiteLaptop.MaxAgree.proposition_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:18:39.25621+00:00
-- url     : https://prove2.me/theorems/7f0b7f29-0235-42b2-9ac7-1b09cec6dbdb
-- title:
--   Proposition 2.4 — finitely many coefficient bounds give P̲_{k,M}(ρ) ≤ P_k(ρ) ≤ P̄_{k,M}(ρ) on [−1, 1]
-- statement:
--   Fix $k\ge1$ and $M\in\mathbb N_0$, and suppose that for each $m=0,\dots,M$ we have bounds $\underline c_{k,m}\le c_{k,m}\le\overline c_{k,m}$ (for $k=1$, since $P_1\equiv1$, the exact values $c_{1,0}=1$, $c_{1,m}=0$ for $m\ge1$ may be used). With $\underline P_{k,M}$ and $\overline P_{k,M}$ the piecewise truncated polynomials of the definition item,
--   $$\underline P_{k,M}(\rho)\le P_k(\rho)\le\overline P_{k,M}(\rho)\qquad\text{for all }\rho\in[-1,1].$$
--   This turns finitely many certified coefficients into rigorous two-sided bounds on the whole collision-probability function.
--
--   **Formalization Note.** The bounds are arbitrary reals `cl m`, `cu m`; only `m ≤ M` is constrained and read.
--
--   Differences from the source:
--   - encoding: two printed branches for ρ ∈ [0,1] and ρ ∈ [−1,0] → the [0,1] branch for ρ ≥ 0, the [−1,0] branch for ρ < 0; reason: the two branches agree at ρ = 0
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), pp. 16–17 (PDF 19–20), Proposition 2.4

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_Hermite
import Definitions.Def_HermiteLaptop_MaxAgree_TruncBounds

namespace HermiteLaptop.MaxAgree

/-- Proposition 2.4: bounds `c̲_{k,m} ≤ c_{k,m} ≤ c̄_{k,m}` for `m ≤ M` give
`P̲_{k,M}(ρ) ≤ P_k(ρ) ≤ P̄_{k,M}(ρ)` on `[−1, 1]`. -/
theorem proposition_2_4 (k : ℕ) (hk : 1 ≤ k) (M : ℕ) (cl cu : ℕ → ℝ)
    (hcl : ∀ m ≤ M, cl m ≤ coeffC k m) (hcu : ∀ m ≤ M, coeffC k m ≤ cu m) :
    ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
      truncLower M cl cu ρ ≤ collisionProb k ρ ∧ collisionProb k ρ ≤ truncUpper M cl cu ρ := by sorry

end HermiteLaptop.MaxAgree
