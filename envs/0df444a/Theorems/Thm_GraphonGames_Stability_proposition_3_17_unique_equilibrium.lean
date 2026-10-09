-- Prove2me | Theorems.Thm_GraphonGames_Stability_proposition_3_17_unique_equilibrium
-- name    : GraphonGames.Stability.proposition_3_17_unique_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:25.150256+00:00
-- url     : https://prove2.me/theorems/725ac376-4945-4056-baa9-1e4e47dc7ff4
-- title:
--   Proposition 3.17 — existence and uniqueness under condition (17)
-- statement:
--   Assume Assumptions 1 and 4. Let $w$ be a graphon with operator $W$ such that $\sqrt{c_z}\|W\|<1$ and
--
--   $$
--   \frac{\ell_J}{\ell_c}\,
--   \frac{\sqrt{c_\alpha}\|W\|}{1-\sqrt{c_z}\|W\|}<1.
--   $$
--
--   Then the graphon game has a Nash equilibrium, and every Nash equilibrium is equal to it almost everywhere.
--
--   This gives the unique equilibrium named in the stability theorem.
--
--   **Formalization Note** Equilibrium uses the pointwise minimization condition of Proposition 3.6 and carries an aggregate satisfying (6). Uniqueness is of $L^2$ classes; no boundedness Assumption 5 is imposed.
-- source:
--   Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, p. 15, Proposition 3.17 and (17)

import Mathlib
import Definitions.Def_GraphonGames_Stability_Setting

open MeasureTheory

namespace GraphonGames.Stability

theorem proposition_3_17_unique_equilibrium
    (b : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (μ0 : Measure ℝ) (cα cz ℓc ℓJ : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz)
    (h4 : GraphonGames.Existence.Asm4 (GraphonGames.Existence.cost b f μ0) ℓc ℓJ)
    (w : I → I → ℝ) (hw : IsGraphon w)
    (hW : Real.sqrt cz * (opNorm w).toReal < 1)
    (h17 : ℓJ / ℓc *
      (Real.sqrt cα * (opNorm w).toReal /
        (1 - Real.sqrt cz * (opNorm w).toReal)) < 1) :
    ∃ α, IsNash w b f μ0 α ∧
      ∀ α', IsNash w b f μ0 α' → α' =ᵐ[volume] α := by sorry

end GraphonGames.Stability
