-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_4_16
-- name    : GraphonCheeger.Supplement.theorem_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:32:46.046967+00:00
-- url     : https://prove2.me/theorems/db645faf-cafe-46a7-b103-1c98a62794f7
-- title:
--   Theorem 4.16 — $\mathrm{MS}_{k,\mathrm{mix}}(W)=\mathrm{MS}_{k,\mathrm{pure}}(W)$ for graphons on $[0,1]$
-- statement:
--   Fix $k\ge2$ and let $W$ be a graphon on $[0,1]$ with Lebesgue measure. Then
--   $$
--   \mathrm{MS}_{k,\mathrm{mix}}(W)=\mathrm{MS}_{k,\mathrm{pure}}(W).
--   $$
--
--   On $[0,1]$ the balanced fractional relaxation of minimum $k$-section has the same value as the infimum over measurable partitions into $k$ sets of measure $1/k$.
--
--   **Formalization Note** $\mathrm{MS}_{k,\mathrm{pure}}$ takes values in the extended reals, with $\inf\emptyset=+\infty$ (4.43); the equality is in `EReal`, with the real number $\mathrm{MS}_{k,\mathrm{mix}}(W)$ cast.
--
--   Differences from the source:
--   - encoding: [0, 1] with Lebesgue measure λ → unitInterval with volume and the Borel σ-field; reason: Remark 3.3: the Borel and Lebesgue σ-fields give the same results up to a.e. equality
--   - encoding: MS_{k,pure}(W) with inf ∅ = +∞ → EReal-valued minSectionPure; the equality is stated in EReal; reason: the convention of (4.43); on [0, 1] both sides are finite
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 4.16, p.40 (PDF p.40)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_kSection

open MeasureTheory

namespace GraphonCheeger.Supplement

/-- Theorem 4.16, p.40 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `W` be a graphon on `[0, 1]`. Then `MS_{k,mix}(W) = MS_{k,pure}(W)`.

**Formalization Note.** `k ≥ 2` is fixed (§4.2). `[0, 1]` carries Lebesgue measure. `MS_{k,pure}`
is valued in `EReal` with `inf ∅ = +∞` (4.43), so the equality is in `EReal`, with the real
number `MS_{k,mix}(W)` cast. -/
theorem theorem_4_16 (k : ℕ) (hk : 2 ≤ k) (W : unitInterval → unitInterval → ℝ)
    (hW : IsGraphon W) :
    ((minSectionMix k volume W : ℝ) : EReal) = minSectionPure k volume W := by sorry

end GraphonCheeger.Supplement
