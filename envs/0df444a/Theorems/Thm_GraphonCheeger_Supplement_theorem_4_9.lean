-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_4_9
-- name    : GraphonCheeger.Supplement.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:30:16.169187+00:00
-- url     : https://prove2.me/theorems/f48d698c-a21e-452e-9844-4331db4a149d
-- title:
--   Theorem 4.9 — $\mathrm{MC}_{\mathrm{pure}}(W)=\mathrm{MC}_{\mathrm{mix}}(W)$ for graphons on $[0,1]$
-- statement:
--   Let $W$ be a graphon on $[0,1]$ with Lebesgue measure. Then
--   $$
--   \mathrm{MC}_{\mathrm{pure}}(W)=\mathrm{MC}_{\mathrm{mix}}(W).
--   $$
--
--   On the atomless space $[0,1]$ fractional cuts give no advantage over measurable cuts, in contrast with atomic spaces (Example 4.4).
--
--   Differences from the source:
--   - encoding: [0, 1] with Lebesgue measure λ → unitInterval with volume and the Borel σ-field; reason: Remark 3.3: the Borel and Lebesgue σ-fields give the same results up to a.e. equality
--   - encoding: mixed 2-colouring Ψ = (ψ, 1 − ψ) → ψ : Ω → [0, 1] measurable (base IsColouring); C(W, Ψ) is the base cutVal; reason: the identification the paper makes (pp.31–32)
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 4.9, p.36 (PDF p.36)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_maxCut

open MeasureTheory

namespace GraphonCheeger.Supplement

/-- Theorem 4.9, p.36 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `W` be a graphon on `[0, 1]`. Then `MC_pure(W) = MC_mix(W)`.

**Formalization Note.** `[0, 1]` is `unitInterval` with Lebesgue measure (`volume`). -/
theorem theorem_4_9 (W : unitInterval → unitInterval → ℝ) (hW : IsGraphon W) :
    maxCutPure volume W = maxCutMix volume W := by sorry

end GraphonCheeger.Supplement
