-- Prove2me | Theorems.Thm_JeroslowMLP_Value_lemma_3_1
-- name    : JeroslowMLP.Value.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:59:25.011274+00:00
-- url     : https://prove2.me/theorems/61bddf8e-2983-412b-a339-aaecd0b6728f
-- title:
--   Lemma 3.1, p. 150 — for binary atoms, L_F has a unique binary solution w, and F is true iff x(F) = 1
-- statement:
--   Let $F$ be a propositional formula over blocked atoms, and let $\alpha$ be a truth assignment of the atoms; set each atom variable to $x_{kj}=1$ if $\alpha(X_{kj})$ is true and $x_{kj}=0$ otherwise. Then:
--
--   1. there is exactly one binary assignment $w$ of the node variables $x(G)$ such that $(x^1,\dots,x^p,w)$ satisfies $L_F$;
--   2. for every binary $w$ satisfying $L_F$ with these atom values,
--   $$F(\alpha)\ \text{is true}\iff x(F)=1 .$$
--
--   This is the correctness of the linear encoding of a formula: on binary inputs, $L_F$ computes $F$.
--
--   **Formalization Note** "Unique binary assignment" is unique existence among binary node vectors. If $F$ is atomic there are no node variables and $x(F)$ is the atom's variable.
-- source:
--   Jeroslow, The polynomial hierarchy and a simple model for competitive analysis, Math. Programming 32 (1985), p. 150, Lemma 3.1, (3.2)

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Formula
import Definitions.Def_JeroslowMLP_Value_Multilevel

namespace JeroslowMLP.Value

theorem lemma_3_1 (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n)) (α : Atom p n → Bool) :
    (∃! w : F.Node → ℝ, (∀ g, IsBinary (w g)) ∧
        F.LSys (fun a => if α a then 1 else 0) w) ∧
    ∀ w : F.Node → ℝ, (∀ g, IsBinary (w g)) →
      F.LSys (fun a => if α a then 1 else 0) w →
      (F.eval α = true ↔ F.nodeVal (fun a => if α a then 1 else 0) w = 1) := by sorry

end JeroslowMLP.Value
