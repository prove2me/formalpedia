-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_4_10
-- name    : GraphonCheeger.Supplement.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:30:46.86512+00:00
-- url     : https://prove2.me/theorems/4bad73af-aa8f-4621-a58b-be7ee436faf9
-- title:
--   Theorem 4.10 — the mixed maximum cut is attained
-- statement:
--   Let $W$ be a graphon on a probability space $(\Omega,\mathcal F,\mu)$. Then the supremum defining $\mathrm{MC}_{\mathrm{mix}}(W)$ is attained: there exists a mixed 2-colouring $\Psi=(\psi,1-\psi)$ of $W$ with
--   $$
--   \mathrm{MC}(W)=C(W,\Psi)=\iint_{\Omega^2}W(x,y)\psi(x)(1-\psi(y))\,d\mu(x)\,d\mu(y).
--   $$
--
--   Whether the pure supremum is always attained is left open in Remark 4.11.
--
--   Differences from the source:
--   - encoding: mixed 2-colouring Ψ = (ψ, 1 − ψ) → ψ : Ω → [0, 1] measurable (base IsColouring); C(W, Ψ) is the base cutVal; reason: the identification the paper makes (pp.31–32)
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 4.10, p.36 (PDF p.36)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_maxCut

open MeasureTheory

universe u

namespace GraphonCheeger.Supplement

/-- Theorem 4.10, p.36 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `W` be a graphon on a probability space `(Ω, F, µ)`. Then the
supremum in (4.16) is attained: there exists a mixed colouring `Ψ` of `W` with `MC(W) = C(W, Ψ)`.

**Formalization Note.** A mixed 2-colouring `Ψ = (ψ, 1 − ψ)` is identified with `ψ` (base
`IsColouring`), and `C(W, Ψ)` is the base `cutVal` (4.14). -/
theorem theorem_4_10 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Ω → ℝ) (hW : IsGraphon W) :
    ∃ ψ : Ω → ℝ, IsColouring ψ ∧ maxCutMix μ W = cutVal μ W ψ := by sorry

end GraphonCheeger.Supplement
