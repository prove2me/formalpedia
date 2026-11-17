-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_4_17
-- name    : GraphonCheeger.Supplement.theorem_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:33:12.2711+00:00
-- url     : https://prove2.me/theorems/7ccd0a23-41ee-4996-a984-3d158426d655
-- title:
--   Theorem 4.17 — the balanced mixed minimum $k$-section is attained
-- statement:
--   Let $W$ be a graphon on a probability space $(\Omega,\mathcal F,\mu)$ and fix $k\ge2$. Then the extremum in (4.48) is attained: there exists a balanced mixed $k$-colouring $\Psi$ of $W$ (that is, $\int\psi_i\,d\mu=1/k$ for every $i$) with
--   $$
--   \mathrm{MS}_k(W)=C_k(W,\Psi)=\sum_{1\le i<j\le k}\iint_{\Omega^2}W(x,y)\psi_i(x)\psi_j(y)\,d\mu(x)\,d\mu(y).
--   $$
--
--   **Formalization Note** The page writes "the supremum in (4.48)", but (4.48) is an infimum; the statement follows the theorem's own "in other words" sentence.
--
--   Differences from the source:
--   - reading: "the supremum in (4.48) is attained" → the infimum in (4.48) is attained: ∃ balanced Ψ with MS_k(W) = C_k(W, Ψ); reason: (4.48) defines MS_{k,mix} as an infimum, and the theorem's "In other words" sentence states attainment of that infimum
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 4.17, p.41 (PDF p.41)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_kSection

open MeasureTheory

universe u

namespace GraphonCheeger.Supplement

/-- Theorem 4.17, p.41 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `W` be a graphon on a probability space `(Ω, F, µ)` and fix `k ≥ 2`.
Then the extremum in (4.48) is attained: there exists a balanced mixed colouring `Ψ` of `W` with
`MS_k(W) = C_k(W, Ψ)`.

**Formalization Note.** The page says "the supremum in (4.48)", but (4.48) is an infimum; the
statement follows the theorem's own "in other words" sentence. -/
theorem theorem_4_17 (k : ℕ) (hk : 2 ≤ k) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : Ω → Ω → ℝ) (hW : IsGraphon W) :
    ∃ Ψ : Ω → Fin k → ℝ, IsKColouring Ψ ∧ IsBalanced μ Ψ ∧
      minSectionMix k μ W = colScore μ W Ψ := by sorry

end GraphonCheeger.Supplement
