-- Prove2me | Theorems.Thm_OracleStateHSP_theorem_4_4
-- name    : OracleStateHSP.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:36:46.862207+00:00
-- url     : https://prove2.me/theorems/18d0f7ba-7454-4fdd-90f8-72f4a60c437a
-- title:
--   Theorem 4.4 (Adversary characterization [Bel15, Theorem 37])
-- statement:
--   There are universal constants $c_2 > c_1 > 0$ such that, for all finite sets $X$ and $E$ with $E$ nonempty, every $s : X \to E$ and every family of unitaries $\{O_x\}_{x \in X}$ on a finite-dimensional $\mathcal H_S$,
--   $$
--   c_1\, \gamma_2\bigl(1_{s(x)\ne s(y)} \bigm| (O_x - O_y)_{x,y}\bigr) \;\le\; Q\bigl(s, \{O_x\}\bigr) \;\le\; c_2\, \gamma_2\bigl(1_{s(x)\ne s(y)} \bigm| (O_x - O_y)_{x,y}\bigr),
--   $$
--   where $Q$ is the bounded-error query complexity in the model of Definition 4.1 and $\gamma_2$ is the relative $\gamma_2$ norm. This is eq. (50).
--
--   The paper cites the theorem from Belovs (*Variations on quantum adversary*, arXiv:1504.06943, Theorem 37) and does not prove it. It is used twice: at $\varepsilon = 1$ to turn Simon's bound into a value of $\gamma_2$, and for general $\varepsilon$ to turn the rescaled $\gamma_2$ back into a query bound.
--
--   Differences from the source:
--   - reading: the relative γ2 norm (not defined in the paper) → Belovs's definition: the infimum of max(max‖u_x‖², max‖v_y‖²) over factorizations A_xy = ⟨u_x, (Δ_xy ⊗ I) v_y⟩; reason: the paper describes the norm as this minimum-cost factorization and cites Belovs for it
--   - encoding: Q a number, γ2 a number → Q in ℕ∞ cast to ℝ≥0∞, γ2 in ℝ≥0∞; reason: infeasibility and the absence of an algorithm are ∞, as both sides of (50) require
--   - encoding: a finite answer set E → a finite nonempty type E; reason: an empty E forces X = ∅, the empty problem, where no output map into ∅ exists (Q = ∞) while γ2 = 0; nonemptiness excludes only this undefined case
--   - encoding: every family of unitaries {O_x} → O : X → Matrix Q Q ℂ with the hypothesis that every O_x is unitary, X, E, Q finite types in universe 0; reason: finite sets and finite-dimensional registers are represented by finite types
--   - encoding: measuring a designated output register → a whole-register computational-basis measurement followed by an output map out; reason: a register measurement is such a map, and out(z) can be written into an output register by one final permutation unitary
--   - encoding: finite-dimensional spaces S and W → S = Fin a, W = Fin b for arbitrary a, b; reason: only the dimensions of S and W matter
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Theorem 4.4, eq. (50), p.36 (cited: [Bel15, Theorem 37])

import Mathlib
import Definitions.Def_OracleStateHSP_queryComplexity
import Definitions.Def_OracleStateHSP_answerNe
import Definitions.Def_OracleStateHSP_relGamma2
open scoped ENNReal

namespace OracleStateHSP

/-- Theorem 4.4 of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.36 (adversary characterization, cited there from A. Belovs,
*Variations on quantum adversary*, arXiv:1504.06943, Theorem 37, and not proved in the paper):
there are universal constants `c₂ > c₁ > 0` such that, for every `s : X → E` and every family of
unitaries `{O_x}_{x ∈ X}`,
`c₁ γ₂(1_{s(x)≠s(y)} | (O_x − O_y)_{x,y}) ≤ Q(s, {O_x}) ≤ c₂ γ₂(1_{s(x)≠s(y)} | (O_x − O_y)_{x,y})`
(eq. (50)).

**Formalization Note.** `X` and `E` are finite (Definition 4.3), and `E` is nonempty: an empty
answer set forces `X = ∅`, where `γ₂ = 0` but no output map into `∅` exists, so `Q = ⊤`; `Q` is the bounded-error query
complexity in the model of Definition 4.1 (forward and inverse queries, direct-sum control) with
values in `ℕ∞`, cast to `ℝ≥0∞`; `γ₂` takes values in `ℝ≥0∞`. The constants are quantified before
the types. The instance, answer and query types range over `Type` (universe 0). -/
theorem theorem_4_4 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧
      ∀ (X E Q : Type) [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] [Nonempty E] [Fintype Q]
        [DecidableEq Q] (s : X → E) (O : X → Matrix Q Q ℂ),
        (∀ x, O x ∈ Matrix.unitaryGroup Q ℂ) →
        ENNReal.ofReal c₁ * relGamma2 (answerNe s) (fun x y => O x - O y) ≤
            (queryComplexity O s : ℝ≥0∞) ∧
          (queryComplexity O s : ℝ≥0∞) ≤
            ENNReal.ofReal c₂ * relGamma2 (answerNe s) (fun x y => O x - O y) := by sorry

end OracleStateHSP
