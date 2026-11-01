-- Prove2me | Theorems.Thm_GibbsCongestion_proposition_2_5
-- name    : GibbsCongestion.proposition_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:02:14.164839+00:00
-- url     : https://prove2.me/theorems/e6b25110-f886-4ab3-a9ef-95f212ab1c5f
-- title:
--   Proposition 2.5 (Brändén and Huh): polarization preserves homogeneity and SLC
-- statement:
--   Let $\kappa\in\mathbb Z^n_{\ge0}$. If $p\in R_\kappa[x_i]$ (degree at most $\kappa_i$ in each $x_i$) is $d$-homogeneous and strongly log-concave, then its polarization $\Pi_\kappa(p)$ is multi-affine (it lies in $R^a_\kappa[x_{ij}]$), $d$-homogeneous and strongly log-concave.
--
--   Applied to (11) with $\kappa=(n,\dots,n)$ it makes the polarized generating polynomial, a weighting of the bases of the $n$-uniform matroid on $\mathcal P\times[n]$, strongly log-concave.
--
--   Differences from the source:
--   - reading: log-concave on a subset S ⊆ ℝⁿ≥0 (S unspecified) → log-concave on the open positive orthant; reason: the convention of the cited works (Anari et al.; Brändén–Huh)
--   - encoding: variables x_ij, 1 ≤ i ≤ n, 1 ≤ j ≤ κ_i → variables indexed by the sigma type Σ i, Fin (κ i); reason: the same variables; a variable of an index i with κ_i = 0 does not exist in either
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Proposition 2.5, p.10

import Mathlib
import Definitions.Def_GibbsCongestion_IsSLC
import Definitions.Def_GibbsCongestion_polarization

namespace GibbsCongestion

/-- **Proposition 2.5** (Brändén and Huh) (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Proposition 2.5, p.10). If `p` is
`d`-homogeneous and strongly log-concave over `R_κ[x_i]` (degree at most `κ_i` in each `x_i`), then
its polarization `Π_κ(p)` is `d`-homogeneous and strongly log-concave over `R^a_κ[x_{ij}]`.

**Formalization Note** The variables `x_{ij}`, `1 ≤ j ≤ κ_i`, are indexed by `Σ i, Fin (κ i)`. Membership
in `R^a_κ[x_{ij}]`, the multi-affine polynomials, is the first conjunct. -/
theorem proposition_2_5 {σ : Type*} [Fintype σ] (κ : σ → ℕ) (d : ℕ) (p : MvPolynomial σ ℝ)
    (hκ : ∀ m ∈ p.support, ∀ i, m i ≤ κ i) (hhom : p.IsHomogeneous d) (hslc : IsSLC p) :
    (∀ m ∈ (polarization κ p).support, ∀ v, m v ≤ 1) ∧
      (polarization κ p).IsHomogeneous d ∧ IsSLC (polarization κ p) := by sorry

end GibbsCongestion
