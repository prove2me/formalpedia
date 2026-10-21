-- Prove2me | Theorems.Thm_IntertempDUI_Finite_theorem_1
-- name    : IntertempDUI.Finite.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:52.542404+00:00
-- url     : https://prove2.me/theorems/9a507bea-e08c-4e08-8cf9-308872f74b5d
-- title:
--   Theorem 1 — discounted utility representation and uniqueness
-- statement:
--   On a finite horizon $[0,T]$ with $T>0$, let $\mathcal X$ be connected and let $\mathcal A$ contain every constant continuous trajectory. Assume each primitive interval preference is complete, transitive, nontrivial, and defined on restrictions, and assume (R) and (MinEqn). Then the eight axioms are equivalent to existence of a discounted utility integral representation. The normalized time weight $\rho$ is unique on $[0,T]$, while any other representing utility is $u\mapsto a u+b$ with $a>0$.
--
--   $$\bigwedge\{(ISep),(LSep),(StEq),(C),(Dom),(CIP),(TC),(Eph)\}\Longleftrightarrow\exists(\rho,u)\text{ satisfying (7)}.$$
--
--   The statement is a step toward the finite-horizon characterization in Theorem 1.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, SSRN 3232014 (August 10, 2018), p. 13, Theorem 1; https://ssrn.com/abstract=3232014

import Mathlib
import Definitions.Def_IntertempDUI_Finite_DUI

namespace IntertempDUI.Finite

/-- Theorem 1, p. 13: finite-horizon discounted utility representation and uniqueness. -/
theorem theorem_1 {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (hR : Richness A pref) (hM : MinEqn A pref) :
    ((ISep A pref ∧ LSep A pref ∧ StEq A pref ∧ CondC pref ∧
      Dom A pref ∧ CIP A pref ∧ TC A pref ∧ Eph A pref) ↔
      ∃ (ρ : StieltjesFunction ℝ) (u : X → ℝ), IsDUIRep (le_of_lt hT) A pref ρ u) ∧
    (∀ ρ u ρ' u', IsDUIRep (le_of_lt hT) A pref ρ u →
      IsDUIRep (le_of_lt hT) A pref ρ' u' →
      Set.EqOn (ρ : ℝ → ℝ) (ρ' : ℝ → ℝ) (Set.Icc 0 T) ∧
      ∃ a b : ℝ, 0 < a ∧ ∀ x : X, u' x = a * u x + b) := by sorry

end IntertempDUI.Finite
