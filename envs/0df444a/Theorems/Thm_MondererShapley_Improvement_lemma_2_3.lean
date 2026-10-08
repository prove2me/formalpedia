-- Prove2me | Theorems.Thm_MondererShapley_Improvement_lemma_2_3
-- name    : MondererShapley.Improvement.lemma_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:18.551489+00:00
-- url     : https://prove2.me/theorems/57115218-c3e9-460e-9bcd-8aaf7355bfd6
-- title:
--   Lemma 2.3 — finite ordinal potential games have the FIP
-- statement:
--   Let $\Gamma$ be a finite strategic-form game. If $\Gamma$ admits an ordinal potential $P$ satisfying (2.1), then every strict unilateral improvement path is finite:
--
--   $$
--   \exists P\;\text{ordinal for }\Gamma\quad\Longrightarrow\quad\Gamma\text{ has the FIP}.
--   $$
--
--   This is the paper's finite-game termination statement and supplies the forward potential-to-FIP comparison for Lemma 2.5.
--
--   **Formalization Note** Both the player set and every strategy set are finite; no nonemptiness is required.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 128 (PDF p. 5), Lemma 2.3

import Mathlib
import Definitions.Def_MondererShapley_Improvement_IsOrdinalPotential
import Definitions.Def_MondererShapley_Improvement_HasFIP

namespace MondererShapley.Improvement

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- Lemma 2.3 (p. 128): a finite ordinal potential game has the FIP. -/
theorem lemma_2_3 [Fintype ι] [∀ i, Fintype (Y i)]
    (u : ι → (∀ i, Y i) → ℝ) (h : ∃ P, IsOrdinalPotential u P) :
    HasFIP u := by sorry

end MondererShapley.Improvement
