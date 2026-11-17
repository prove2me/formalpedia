-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_5_10
-- name    : GraphonCheeger.Supplement.theorem_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:34:34.887667+00:00
-- url     : https://prove2.me/theorems/f370c1b0-5da1-43da-8eca-bd57dd12e3c3
-- title:
--   Theorem 5.10 — $\hat q^*_{\kappa,\mathrm{pure}}=\hat q^*_{\kappa,\mathrm{mix}}$ and $\hat q^*_{\mathrm{pure}}=\hat q^*_{\mathrm{mix}}$ on $[0,1]$
-- statement:
--   Let $W$ be an uncoloured graphon on $[0,1]$ with Lebesgue measure $\lambda$. Then
--   $$
--   \hat q^*_{\kappa,\mathrm{pure}}(W)=\hat q^*_{\kappa,\mathrm{mix}}(W)\quad\text{for every }\kappa\ge1,
--   $$
--   and consequently $\hat q^*_{\mathrm{pure}}(W)=\hat q^*_{\mathrm{mix}}(W)$.
--
--   On $[0,1]$, the graphon modularity of Klimm, Jones and Schaub (pure colourings) agrees with the mixed modularity used in this paper.
--
--   Differences from the source:
--   - encoding: [0, 1] with Lebesgue measure λ → unitInterval with volume and the Borel σ-field; reason: Remark 3.3: the Borel and Lebesgue σ-fields give the same results up to a.e. equality
--   - encoding: colourings Ψ : Ω → Δκ, colours [κ]; pure colourings χ : Ω → [κ] → Ψ : Ω → Fin κ → ℝ with measurable nonnegative coordinates summing to 1 (IsKColouring); pure χ measurable with the point-mass colouring ofColour χ; reason: the same objects (Definition 2.1, p.7), with colours numbered 0, …, κ − 1
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 5.10, p.57 (PDF p.57)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_graphonModularity

open MeasureTheory

namespace GraphonCheeger.Supplement

/-- Theorem 5.10, p.57 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `W` be an uncoloured graphon on `[0, 1]` (with Lebesgue measure `λ`).
Then `q̂*_{κ,pure}(W) = q̂*_{κ,mix}(W)` for every `κ ≥ 1`, and consequently
`q̂*_pure(W) = q̂*_mix(W)`.

**Formalization Note.** `q̂*_{κ,mix} = modK κ` (5.34), `q̂*_{κ,pure} = modPureK κ` (5.36),
`q̂*_mix = modW` (5.35), `q̂*_pure = modPure` (5.37). -/
theorem theorem_5_10 (W : unitInterval → unitInterval → ℝ) (hW : IsGraphon W) :
    (∀ κ : ℕ, 1 ≤ κ → modPureK κ volume W = modK κ volume W) ∧
    modPure volume W = modW volume W := by sorry

end GraphonCheeger.Supplement
