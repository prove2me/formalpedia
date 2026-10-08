-- Prove2me | Theorems.Thm_MFGPlanning_Existence_lemma_1
-- name    : MFGPlanning.Existence.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T20:00:48.901628+00:00
-- url     : https://prove2.me/theorems/46727805-9d93-462b-a8d7-ea7844995d13
-- title:
--   Lemma 1 — $\Theta$ convex and continuous, $\Sigma$ convex and l.s.c., constraint qualification
-- statement:
--   Assume (24) and (G4). Then the functional $\Theta$ on the space of dual variables $(\alpha,\beta)$ is finite, convex and continuous; the functional $\Sigma$ is convex and lower semicontinuous; and the following constraint qualification holds: there exists $(\alpha,\beta)$ with
--   $$\Sigma(\alpha,\beta) < +\infty \quad\text{and}\quad \Theta(\alpha,\beta) < +\infty.$$
--
--   This is the hypothesis under which the Fenchel–Rockafellar theorem applies to $\Theta$ and $\Sigma$, giving the no-gap equality of Theorem 1 and the existence of a primal minimizer.
--
--   **Formalization Note** "$\Theta$ is convex and continuous" is stated for a real function equal to $\Theta$ on the space $\mathbb R^{N_T\times N_h^2}\times\mathbb R^{4N_T\times N_h^2}$ (product topology). Convexity of the extended-valued $\Sigma$ means convexity of its epigraph; lower semicontinuity is Mathlib's `LowerSemicontinuous` for `EReal`-valued functions. Of the standing assumptions of §3.1, only (24) and (G4) are assumed.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), Lemma 1, p. 8

import Mathlib
import Definitions.Def_MFGPlanning_Existence_Grid
import Definitions.Def_MFGPlanning_Existence_Hyp
import Definitions.Def_MFGPlanning_Existence_Duality

namespace MFGPlanning.Existence

/-- Lemma 1 of Achdou, Camilli, Capuzzo-Dolcetta, hal-00465404v1 (2010), §3.1, p. 8 (PDF 9):
`Θ` is convex and continuous; `Σ` is convex and lower semicontinuous; there exists `(α, β)` with
`Σ(α, β) < +∞` (and `Θ(α, β) < +∞`).

Formalization Note: stated under (24) and (G4), the hypotheses the claim uses among the standing ones
of §3.1. "`Θ` convex and continuous" is said of a real function `θ` equal to `Θ` (so `Θ` is finite).
Convexity of the `EReal`-valued `Σ` is convexity of its epigraph. -/
theorem lemma_1 (d : Data) (hW : A24 d) (hG4 : G4 d) :
    (∃ θ : (Fin d.NT → d.Pt → ℝ) × (Fin d.NT → d.Pt → Fin 4 → ℝ) → ℝ,
        (∀ α β, Theta d α β = (θ (α, β) : EReal)) ∧ ConvexOn ℝ Set.univ θ ∧ Continuous θ) ∧
    Convex ℝ {x : ((Fin d.NT → d.Pt → ℝ) × (Fin d.NT → d.Pt → Fin 4 → ℝ)) × ℝ |
        SigmaF d x.1.1 x.1.2 ≤ (x.2 : EReal)} ∧
    LowerSemicontinuous
        (fun x : (Fin d.NT → d.Pt → ℝ) × (Fin d.NT → d.Pt → Fin 4 → ℝ) => SigmaF d x.1 x.2) ∧
    ∃ (α : Fin d.NT → d.Pt → ℝ) (β : Fin d.NT → d.Pt → Fin 4 → ℝ),
      SigmaF d α β < ⊤ ∧ Theta d α β < ⊤ := by sorry

end MFGPlanning.Existence
