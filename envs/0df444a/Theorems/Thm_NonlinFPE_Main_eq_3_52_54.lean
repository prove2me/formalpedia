-- Prove2me | Theorems.Thm_NonlinFPE_Main_eq_3_52_54
-- name    : NonlinFPE.Main.eq_3_52_54
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:45.674956+00:00
-- url     : https://prove2.me/theorems/21101861-3f60-44ba-9983-d42897513ce3
-- title:
--   (3.52)–(3.54), proof of Lemma 3.6, p. 22 — under (H1)′–(H3)′, the resolvent of A₁ is an L¹ contraction, preserves mass and positivity
-- statement:
--   Assume (H1)′–(H3)′ and let $A_1$ be the operator (3.42). Then for all $\lambda > 0$ and $f, f_1, f_2 \in L^1$:
--   $$|(I+\lambda A_1)^{-1}f_1 - (I+\lambda A_1)^{-1}f_2|_1 \le |f_1 - f_2|_1, \tag{3.52}$$
--   $$\int_{\mathbb R^d}(I+\lambda A_1)^{-1}f\,dx = \int_{\mathbb R^d}f\,dx, \tag{3.53}$$
--   $$(I+\lambda A_1)^{-1}f \ge 0 \ \text{ a.e. if } f \ge 0 \text{ a.e.} \tag{3.54}$$
--
--   These give, through the exponential formula, the properties (3.36)–(3.38) of the semigroup in Theorem 3.7.
--
--   **Formalization Note** Stated for arbitrary solutions $u + \lambda v = f$, $v = A_1u$ (existence is Lemma 3.6), so no resolvent is chosen.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, §3.2, proof of Lemma 3.6, p. 22, (3.52)–(3.54)

import Mathlib
import Definitions.Def_NonlinFPE_Main_Setting
import Definitions.Def_NonlinFPE_Main_MAccretive

open MeasureTheory
open scoped NNReal

namespace NonlinFPE.Main

open EthierKurtz

/-- (3.52)–(3.54), proof of Lemma 3.6, p. 22, under (H1)′–(H3)′: for every `λ > 0`, solutions of
`u + λA₁u = f` satisfy the `L¹` contraction (3.52), mass conservation (3.53) and
positivity (3.54). -/
theorem eq_3_52_54 {d : ℕ} (a' : Fin d → Fin d → ℝ → ℝ) (b' : Fin d → ℝ → ℝ)
    (hDeg : HypDeg a' b') :
    (∀ lam : ℝ, 0 < lam → ∀ u₁ v₁ f₁ u₂ v₂ f₂ : SDEState d →₁[volume] ℝ,
      opA (liftA a') (liftB b') u₁ v₁ → u₁ + lam • v₁ = f₁ →
      opA (liftA a') (liftB b') u₂ v₂ → u₂ + lam • v₂ = f₂ →
        ‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖) ∧
    (∀ lam : ℝ, 0 < lam → ∀ u v f : SDEState d →₁[volume] ℝ,
      opA (liftA a') (liftB b') u v → u + lam • v = f → ∫ x, u x = ∫ x, f x) ∧
    (∀ lam : ℝ, 0 < lam → ∀ u v f : SDEState d →₁[volume] ℝ,
      opA (liftA a') (liftB b') u v → u + lam • v = f → 0 ≤ᵐ[volume] (f : SDEState d → ℝ) →
        0 ≤ᵐ[volume] (u : SDEState d → ℝ)) := by sorry

end NonlinFPE.Main
