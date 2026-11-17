-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_4_34
-- name    : GraphonCheeger.Supplement.theorem_4_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:33:35.05398+00:00
-- url     : https://prove2.me/theorems/f4cb79e8-1858-48e5-a15a-5229aa934e06
-- title:
--   Theorem 4.34 — $h_{\mathrm{pure}}(W)=h_{\mathrm{mix}}(W)$ for graphons on $[0,1]$ with $\rho_W>0$
-- statement:
--   Let $W$ be a graphon on $[0,1]$ with Lebesgue measure and edge density $\rho_W>0$. Then the pure and mixed Cheeger constants coincide:
--   $$
--   h_{\mathrm{pure}}(W)=h_{\mathrm{mix}}(W),
--   $$
--   where $h_{\mathrm{mix}}(W)=\inf\{C(W,\psi)/D(W,\psi)\}$ over mixed 2-colourings with $D(W,\psi)>0$ and $h_{\mathrm{pure}}(W)$ is the same infimum over pure colourings.
--
--   This complements the mission's goal, Theorem 4.33, which identifies the limit of the graph Cheeger constants as the mixed constant $h(W)$: on $[0,1]$ it is also the infimum over measurable cuts.
--
--   **Formalization Note** $h_{\mathrm{mix}}$ and $h_{\mathrm{pure}}$ are the base `cheegerW` and `cheegerPure`, and $\rho_W$ is the base `density`.
--
--   Differences from the source:
--   - encoding: [0, 1] with Lebesgue measure λ → unitInterval with volume and the Borel σ-field; reason: Remark 3.3: the Borel and Lebesgue σ-fields give the same results up to a.e. equality
--   - encoding: mixed 2-colouring Ψ = (ψ, 1 − ψ) → ψ : Ω → [0, 1] measurable (base IsColouring); C(W, Ψ) is the base cutVal; reason: the identification the paper makes (pp.31–32)
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 4.34, p.50 (PDF p.50)

import Mathlib
import Definitions.Def_GraphonCheeger_cheegerW

open MeasureTheory

namespace GraphonCheeger.Supplement

/-- Theorem 4.34, p.50 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `W` be a graphon on `[0, 1]` with `ρ_W > 0`. Then
`h_pure(W) = h_mix(W)`.

**Formalization Note.** `[0, 1]` carries Lebesgue measure. `h_mix = h` is the base `cheegerW`
(4.83) and `h_pure` the base `cheegerPure`; `ρ_W` is the base `density`. -/
theorem theorem_4_34 (W : unitInterval → unitInterval → ℝ) (hW : IsGraphon W)
    (hρ : 0 < density volume W) :
    cheegerPure volume W = cheegerW volume W := by sorry

end GraphonCheeger.Supplement
