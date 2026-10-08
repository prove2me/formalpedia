-- Prove2me | Theorems.Thm_MFGPlanning_Existence_lemma_3
-- name    : MFGPlanning.Existence.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T20:01:02.527993+00:00
-- url     : https://prove2.me/theorems/acea5798-2a3b-4503-bc0c-e5d47c129152
-- title:
--   Lemma 3 — a primal point where $\Theta^*$, $\Sigma^*(-\cdot)$ are finite and $\Theta^*$ is continuous nearby
-- statement:
--   Assume (G1), (G3), (G4), (G5), (24), $m_0, m_T\in\mathcal K$, and $(m_0)_{i,j} > 0$ for all $i,j$. Then there exists $(M,Z)$ such that
--   $$\Theta^*(M,Z) < +\infty,\qquad \Sigma^*(-M,-Z) < +\infty,$$
--   and $\Theta^*$ is finite and continuous in a neighborhood of $(M,Z)$.
--
--   This is the constraint qualification for the primal problem (30): with it, the Fenchel–Rockafellar theorem applied to $(M,Z)\mapsto\Theta^*(M,Z)$ and $(M,Z)\mapsto\Sigma^*(-M,-Z)$ gives a minimizer of the dual problem.
--
--   **Formalization Note** "Continuous in a neighborhood" is formalized as: some neighborhood $s$ of $(M,Z)$ on which $\Theta^*$ is not $+\infty$ and on which $\Theta^*$ (an `EReal`-valued function) is continuous, matching the proof's "$\Theta^*(M,Z)$ is finite and $\Theta^*$ is continuous in a neighborhood". The standing assumptions of §3.1 are hypotheses ((G2) is not encoded; see the definition of the hypotheses).
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), Lemma 3, p. 9

import Mathlib
import Definitions.Def_MFGPlanning_Existence_Grid
import Definitions.Def_MFGPlanning_Existence_Hyp
import Definitions.Def_MFGPlanning_Existence_Duality

namespace MFGPlanning.Existence

/-- Lemma 3 of Achdou, Camilli, Capuzzo-Dolcetta, hal-00465404v1 (2010), §3.1, p. 9 (PDF 10):
if `(m_0)_{i,j} > 0` for all `i, j`, there exists `(M, Z)` with `Θ^*(M, Z) < +∞`, `Σ^*(−M, −Z) < +∞`,
and `Θ^*` continuous in a neighborhood of `(M, Z)`.

Formalization Note: the standing assumptions of §3.1 ((24), (G1)–(G5) without (G2), `m_0, m_T ∈ 𝒦`)
are hypotheses. "Continuous in a neighborhood" is with finite values, as in the proof ("`Θ^*` is
finite and `Θ^*` is continuous in a neighborhood of `(M, Z)`"). -/
theorem lemma_3 (d : Data) (hG1 : G1 d) (hG3 : G3 d) (hG4 : G4 d) (hG5 : G5 d) (hW : A24 d)
    (hm0 : InK d d.m0) (hmT : InK d d.mT) (hm0pos : ∀ p, 0 < d.m0 p) :
    ∃ (M : Fin d.NT → d.Pt → ℝ) (Z : Fin d.NT → d.Pt → Fin 4 → ℝ),
      ThetaStar d M Z < ⊤ ∧ SigmaStar d (-M) (-Z) < ⊤ ∧
      ∃ s ∈ nhds (M, Z), (∀ x ∈ s, ThetaStar d x.1 x.2 ≠ ⊤) ∧
        ContinuousOn
          (fun x : (Fin d.NT → d.Pt → ℝ) × (Fin d.NT → d.Pt → Fin 4 → ℝ) => ThetaStar d x.1 x.2) s := by sorry

end MFGPlanning.Existence
