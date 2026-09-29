-- Prove2me | Theorems.Thm_HahnSeries_mem_puiseuxRamSubfield_iff
-- name    : HahnSeries.mem_puiseuxRamSubfield_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/81fd5298-524e-5e5a-b70c-9c519bf44611
-- title:
--   Membership in the e-ramified Puiseux subfield
-- statement:
--   Let $K$ be a field, let $e$ be a natural number with $0 < e$, and let $y$ be a Hahn series with rational exponents and coefficients in $K$. The theorem asserts the equivalence of two conditions on $y$. The first is that $y$ lies in [`HahnSeries.puiseuxRamSubfield K he`](def/HahnSeries_RamificationBound.html#L37), the subfield of $K((t^{\mathbb{Q}}))$ defined as the field range of the ring homomorphism [`HahnSeries.puiseuxRamEmb he`](def/HahnSeries_RamificationBound.html#L29) from $K((t^{\mathbb{Z}}))$ to $K((t^{\mathbb{Q}}))$, that is, of the map obtained by transporting the exponent domain along the strictly monotone injection `ramScale e` sending $k \in \mathbb{Z}$ to $k/e \in \mathbb{Q}$; equivalently, $y = x(t^{1/e})$ for some Laurent–Hahn series $x$ with integer exponents. The second is [`HahnSeries.HasRamBound e y`](def/HahnSeries_RamificationBound.html#L32), which by definition says that the support of $y$ is contained in the range of $k \mapsto (k : \mathbb{Q})/e$, i.e. every exponent occurring in $y$ lies in $\tfrac{1}{e}\mathbb{Z}$.
--
--   This is the characterisation of the Puiseux subfield $K((t^{1/e}))$ inside the Hahn field $K((t^{\mathbb{Q}}))$ by bounded denominators of exponents; combined with the fact that the right-hand side is membership in a subfield, it is the source of the closure of `HasRamBound e` under the field operations. It is used in the ramification analysis of places of the modular curves, for instance in the statements that the order of a place divides, or equals one, according as all Hahn-series embeddings satisfy a given ramification bound.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HahnSeries_mem_puiseuxRamSubfield_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HahnSeries.mem_puiseuxRamSubfield_iff {K : Type*} [Field K] {e : ℕ} (he : 0 < e)
    {y : HahnSeries ℚ K} :
    y ∈ HahnSeries.puiseuxRamSubfield K he ↔ HahnSeries.HasRamBound e y := by sorry
