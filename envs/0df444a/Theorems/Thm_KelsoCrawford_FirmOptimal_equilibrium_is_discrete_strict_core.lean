-- Prove2me | Theorems.Thm_KelsoCrawford_FirmOptimal_equilibrium_is_discrete_strict_core
-- name    : KelsoCrawford.FirmOptimal.equilibrium_is_discrete_strict_core
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:18.194386+00:00
-- url     : https://prove2.me/theorems/c75d405d-2989-4603-a1a9-658b0d93bd03
-- title:
--   Proof of Theorem 4, p. 1495 — without ties, every equilibrium of the salary-adjustment process is a discrete strict core allocation
-- statement:
--   Consider a discrete market with salary unit $\delta > 0$ satisfying the standing assumptions — strictly increasing continuous utilities, (MP), (NFL), and (GS) for every firm on the permitted salary vectors — together with the no-ties conditions (NTW) and (NTF). Let a run of the salary-adjustment process R1–R5 stop in round $T$ (no rejections in round $T$), and let $(\phi; s_{1\phi(1)}, \dots, s_{m\phi(m)})$ be the allocation in which every worker accepts the offer he or she holds in round $T$. Then
--
--   $$(\phi; s_{1\phi(1)}, \dots, s_{m\phi(m)}) \text{ is a discrete strict core allocation (D2).}$$
--
--   This is the first half of Theorem 4: the process always stops at a discrete core allocation (Theorem 1), and the no-ties conditions upgrade it to the strict core.
--
--   **Formalization Note** The statement holds for every run, i.e. every admissible tie-breaking by firms and workers, and every stopping round. The standing assumptions of p. 1486, which the sentence does not repeat, are hypotheses.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1495, proof of Theorem 4, first and second paragraphs

import Mathlib
import Definitions.Def_KelsoCrawford_FirmOptimal_Model
import Definitions.Def_KelsoCrawford_FirmOptimal_Process
import Definitions.Def_KelsoCrawford_FirmOptimal_NoTies

namespace KelsoCrawford.FirmOptimal

theorem equilibrium_is_discrete_strict_core
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) (M.gridVectors δ j))
    (hNTW : M.NTW δ) (hNTF : M.NTF δ) :
    ∀ ρ : Run W F, M.IsRun δ ρ → ∀ T, ρ.Stopped T → M.IsStrictCore (M.grid δ) (ρ.outcome T) := by sorry

end KelsoCrawford.FirmOptimal
