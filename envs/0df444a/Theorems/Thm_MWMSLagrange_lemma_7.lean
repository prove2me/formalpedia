-- Prove2me | Theorems.Thm_MWMSLagrange_lemma_7
-- name    : MWMSLagrange.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:02:42.499996+00:00
-- url     : https://prove2.me/theorems/fc3caafc-2074-4020-8e88-0ef3ac614bea
-- title:
--   Lemma 7: one demand changes warehouse $j$'s weighted orders by at most $4\rho_{i_0,j}\bar D$
-- statement:
--   Fix a warehouse $j$, base-stock levels $y_{i,t}\in[0,\bar D]$ and fractions $\rho_{i,j}\in[0,1]$. Let $\omega,\omega'$ be two demand paths with all demands in $[0,\bar D]$ that coincide except possibly at one store–period pair $(i_0,t_0)$, and let $I_{i,t}$, $I'_{i,t}$ be the base-stock inventories (unlimited warehouses) on the two paths. Then
--
--   $$\Big|\sum_{t=1}^T\sum_{i\in\mathcal N_j}\rho_{i,j}(y_{i,t}-I_{i,t})^+-\sum_{t=1}^T\sum_{i\in\mathcal N_j}\rho_{i,j}(y_{i,t}-I'_{i,t})^+\Big|\le 4\rho_{i_0,j}\bar D .$$
--
--   This bounded-differences property is what allows McDiarmid's inequality to be applied to $f_j$.
--
--   **Formalization Note** The paths are full vectors over $[N]\times[T]$; only the coordinates of stores in $\mathcal N_j$ enter the sums.
--
--   Differences from the source:
--   - generalization: neighbouring sample paths of the stores in N_j that differ at exactly one pair (i₀, t₀) ∈ N_j × [T] → paths ω, ω' ∈ [0, D̄]^{[N]×[T]} equal off (i₀, t₀), for any store i₀; reason: the sums read only coordinates of stores in N_j, so equal paths or i₀ ∉ N_j give difference 0; the page's case is included
--   - reading: I_{i,t}, I'_{i,t} (inventory, not defined in the lemma) → base-stock inventory with unlimited warehouses, I_{i,t+1} = (max(y_{i,t}, I_{i,t}) − D_{i,t})^+; reason: the lemma is applied to f_j on p.24, whose I is the inventory under the base-stock levels
--   - reading: D_{i,t} ≤ D̄ (nonnegativity not written) → each law μ_{i,t} has μ_{i,t}([0, D̄]) = 1; reason: the paper treats demand as nonnegative throughout (lost-sales dynamics; proof of Lemma 7, pp.37–38)
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), Lemma 7, p.24

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Nset
import Definitions.Def_MWMSLagrange_ubOnHand

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), Lemma 7, p.24 (bounded
differences of base-stock orders). For a warehouse `j`, base-stock levels `y_{i,t} ∈ [0, D̄]`
and fractions `ρ_{i,j} ∈ [0, 1]`, let `ω, ω'` be two demand paths with values in `[0, D̄]` that
agree except at one pair `(i₀, t₀)`, and let `I, I'` be the corresponding base-stock
inventories (system with unlimited warehouse inventory). Then
`|∑_t ∑_{i∈𝓝_j} ρ_{i,j}(y_{i,t} − I_{i,t})^+ − ∑_t ∑_{i∈𝓝_j} ρ_{i,j}(y_{i,t} − I'_{i,t})^+|
  ≤ 4 ρ_{i₀,j} D̄`.

**Formalization Note.** Demand paths are full vectors `ω : [N] × [T] → ℝ`; the sums only read
the coordinates of the stores in `𝓝_j`. The two paths are only required to agree off
`(i₀, t₀)` (they may also agree there), and `i₀` need not lie in `𝓝_j` (then both sides
are trivially bounded); both are generalizations of the page's "neighboring" paths. -/
theorem lemma_7 {M N T : ℕ} (I : Instance M N) (Dbar : ℝ) (j : Fin M)
    (y : Fin N → Fin T → ℝ) (hy : ∀ i t, 0 ≤ y i t ∧ y i t ≤ Dbar)
    (ρ : Fin N → Fin M → ℝ) (hρ : ∀ i j, 0 ≤ ρ i j ∧ ρ i j ≤ 1)
    (ω ω' : Fin N × Fin T → ℝ) (hω : ∀ p, 0 ≤ ω p ∧ ω p ≤ Dbar)
    (hω' : ∀ p, 0 ≤ ω' p ∧ ω' p ≤ Dbar) (i₀ : Fin N) (t₀ : Fin T)
    (hdiff : ∀ p, p ≠ (i₀, t₀) → ω p = ω' p) :
    |(∑ t : Fin T, ∑ i ∈ I.Nset j, ρ i j * max (y i t - ubOnHand y ω i t) 0)
        - ∑ t : Fin T, ∑ i ∈ I.Nset j, ρ i j * max (y i t - ubOnHand y ω' i t) 0|
      ≤ 4 * ρ i₀ j * Dbar := by sorry

end MWMSLagrange
