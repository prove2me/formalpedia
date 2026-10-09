-- Prove2me | Theorems.Thm_GraphonGames_Stability_theorem_3_20_stability
-- name    : GraphonGames.Stability.theorem_3_20_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:48:51.183978+00:00
-- url     : https://prove2.me/theorems/f5ce253e-8977-43be-aca1-b6a8f9057b54
-- title:
--   Theorem 3.20 — stability of Nash equilibria under graphon changes
-- statement:
--   Assume Assumptions 1, 4, and 5. Let $w$ be a graphon with operator $W$ satisfying $\sqrt{c_z}\|W\|<1$ and condition (17), and let $\alpha$ be its Nash equilibrium. Let $w'$ be any graphon with operator $W'$ satisfying $\sqrt{c_z}\|W'\|<1$, and let $\alpha'$ be any Nash equilibrium for $w'$. Then
--
--   $$
--   \|\alpha-\alpha'\|_{L^2(I)}\leq\kappa\|W-W'\|,\qquad
--   \kappa=\frac{c_0\ell_J(1-\sqrt{c_z}\|W\|)}
--   {(1-\sqrt{c_z}\|W\|)
--   [\ell_c(1-\sqrt{c_z}\|W\|)-\ell_J\sqrt{c_\alpha}\|W\|]}.
--   $$
--
--   This quantifies how much an equilibrium profile can move when the graphon changes. The coefficient uses the original graphon's operator norm and the paper's uncancelled expression.
--
--   **Formalization Note** The equilibrium predicate uses the equivalent third condition of Proposition 3.6 and includes an aggregate for each graphon. The first equilibrium is given as a witness; Proposition 3.17 provides its existence and uniqueness. No condition (17) is imposed on $w'$. The norm of $W-W'$ is the operator norm of $w-w'$, and the inequality is in extended nonnegative reals.
-- source:
--   Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, p. 17, Theorem 3.20

import Mathlib
import Definitions.Def_GraphonGames_Stability_Setting

open MeasureTheory
open scoped ENNReal

namespace GraphonGames.Stability

theorem theorem_3_20_stability
    (b : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (μ0 : Measure ℝ) (cα cz ℓc ℓJ c0 : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz)
    (h4 : GraphonGames.Existence.Asm4 (GraphonGames.Existence.cost b f μ0) ℓc ℓJ)
    (h5 : GraphonGames.Existence.Asm5 b c0)
    (w w' : I → I → ℝ) (hw : IsGraphon w) (hw' : IsGraphon w')
    (hW : Real.sqrt cz * (opNorm w).toReal < 1)
    (h17 : ℓJ / ℓc *
      (Real.sqrt cα * (opNorm w).toReal /
        (1 - Real.sqrt cz * (opNorm w).toReal)) < 1)
    (hW' : Real.sqrt cz * (opNorm w').toReal < 1)
    (α α' : I → ℝ)
    (hα : IsNash w b f μ0 α) (hα' : IsNash w' b f μ0 α') :
    eLpNorm (α - α') 2 volume ≤
      ENNReal.ofReal
        (c0 * ℓJ * (1 - Real.sqrt cz * (opNorm w).toReal) /
          ((1 - Real.sqrt cz * (opNorm w).toReal) *
            (ℓc * (1 - Real.sqrt cz * (opNorm w).toReal) -
              ℓJ * Real.sqrt cα * (opNorm w).toReal))) *
        opNorm (w - w') := by sorry

end GraphonGames.Stability
