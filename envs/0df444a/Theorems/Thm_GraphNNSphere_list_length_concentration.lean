-- Prove2me | Theorems.Thm_GraphNNSphere_list_length_concentration
-- name    : GraphNNSphere.list_length_concentration
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:30.952204+00:00
-- url     : https://prove2.me/theorems/2faf2859-d9ea-4ed4-908b-51223461b757
-- title:
--   Proof of Theorem 3.1(a), list lengths — concentration of $|G_s|,|G_r|$ and $N_\Delta\supseteq G_r$
-- statement:
--   Let $0<r\le s<\pi$. With probability at least $1-2n\exp(-3nF(r)/8)$ over a uniform sample, every data point $x$ satisfies
--   $$|G_s(x)|\le2nF(s)\quad\text{and}\quad|G_r(x)|\le2nF(r).$$
--   Moreover, for every sample and every $\Delta$: if $|G_r(x)|<\Delta$ for every $x$, then the $\Delta$ nearest neighbors of every point include its entire list in $G_r$. Hence $N_\Delta$ contains $G_r$, and it has degree $\min(\Delta,n-1)$, which is $\Delta$ whenever $\Delta\le n-1$.
--
--   These facts show that the threshold and nearest-neighbor graphs of Theorem 3.1(a) meet the edge inclusion and the degree bound.
--
--   Differences from the source:
--   - generalization: r = ρ′ and s = ρ_β or r_γ in the two regimes, for large n → every n ≥ 1, d ≥ 2, 0 < r ≤ s < π; reason: the page argues with (9) only, whose use needs no more; the chosen radii are instances
--   - encoding: "with probability at least" → an explicit measurable data event; reason: so that no outer measure is involved
--   - generalization: "has degree Δ" (with Δ ≤ n − 1, as Δ = ⌈n^β⌉ or ⌈e^{γd}⌉ for large n) → maxDeg (nnGraph X Δ) = min(Δ, n − 1) for every n and Δ; reason: at Δ ≤ n − 1 this is the printed "degree Δ"; at n ≤ Δ the printed equality fails and min(Δ, n − 1) is the true degree
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), proof of Theorem 3.1(a), list lengths, p.23

import Mathlib
import Definitions.Def_GraphNNSphere_capMass
import Definitions.Def_GraphNNSphere_dataLaw
import Definitions.Def_GraphNNSphere_thresholdGraph
import Definitions.Def_GraphNNSphere_nnGraph
import Definitions.Def_GraphNNSphere_Contains
import Definitions.Def_GraphNNSphere_maxDeg

namespace GraphNNSphere

/-- List lengths of threshold graphs and the inclusion `N_Δ ⊇ G_r` (Lu, *Sharp Limits of Graph-Based
Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), proof of
Theorem 3.1(a), list lengths, p.23).

**Formalization Note** The first clause is non-asymptotic. The second is deterministic and uses the
lexicographic tie-breaking of `nnGraph`. The degree of `N_Δ` is `min(Δ, n - 1)`, which is the
page's `Δ` whenever `Δ ≤ n - 1`, as in Theorem 3.1. -/
theorem list_length_concentration :
    (∀ (n d : ℕ) (r s : ℝ), 1 ≤ n → 2 ≤ d → 0 < r → r ≤ s → s < Real.pi →
      ∃ E : Set (Fin n → Sph d), MeasurableSet E ∧
        1 - 2 * (n : ℝ) * Real.exp (-(3 * (n : ℝ) * capMass d r / 8)) ≤ (dataLaw n d E).toReal ∧
        ∀ X ∈ E, ∀ i : Fin n,
          ((thresholdGraph X s i).card : ℝ) ≤ 2 * (n : ℝ) * capMass d s ∧
          ((thresholdGraph X r i).card : ℝ) ≤ 2 * (n : ℝ) * capMass d r) ∧
    (∀ (n d : ℕ) (X : Fin n → Sph d) (r : ℝ) (Δ : ℕ),
      (∀ i, (thresholdGraph X r i).card < Δ) →
        Contains (nnGraph X Δ) (thresholdGraph X r) ∧ maxDeg (nnGraph X Δ) = min Δ (n - 1)) := by sorry

end GraphNNSphere
