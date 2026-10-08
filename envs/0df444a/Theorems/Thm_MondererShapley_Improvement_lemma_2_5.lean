-- Prove2me | Theorems.Thm_MondererShapley_Improvement_lemma_2_5
-- name    : MondererShapley.Improvement.lemma_2_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:13.17476+00:00
-- url     : https://prove2.me/theorems/be7c4676-0865-4aa7-bb80-a507297fdea1
-- title:
--   Lemma 2.5 — FIP iff generalized ordinal potential
-- statement:
--   Let $\Gamma$ be a finite strategic-form game with payoff functions $u^i$. The game has the finite improvement property if and only if it admits a generalized ordinal potential:
--
--   $$
--   \Gamma\text{ has the FIP}\quad\Longleftrightarrow\quad
--   \exists P:Y\to\mathbb R\;\forall i,y^{-i},x,z,\ u^i(y^{-i},x)>u^i(y^{-i},z)\Longrightarrow P(y^{-i},x)>P(y^{-i},z).
--   $$
--
--   This characterizes termination of all strict unilateral improvement paths by a real-valued function that rises along every such step.
--
--   **Formalization Note** The player set and each strategy set are finite. The FIP is expressed as the absence of an infinite improvement path; a path step changes exactly one strategy to a different one.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 129 (PDF p. 6), Lemma 2.5

import Mathlib
import Definitions.Def_MondererShapley_Improvement_HasFIP
import Definitions.Def_MondererShapley_Improvement_IsGenOrdinalPotential

namespace MondererShapley.Improvement

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- Lemma 2.5 (p. 129): the FIP characterizes generalized ordinal potentials in finite games. -/
theorem lemma_2_5 [Fintype ι] [∀ i, Fintype (Y i)]
    (u : ι → (∀ i, Y i) → ℝ) :
    HasFIP u ↔ ∃ P : (∀ i, Y i) → ℝ, IsGenOrdinalPotential u P := by sorry

end MondererShapley.Improvement
