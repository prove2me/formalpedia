-- Prove2me | Theorems.Thm_KelsoCrawford_Process_lemma3_individually_rational
-- name    : KelsoCrawford.Process.lemma3_individually_rational
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:46:18.488027+00:00
-- url     : https://prove2.me/theorems/663dbd39-ddf0-4631-9ba7-5d1734bf5b80
-- title:
--   Lemma 3 — the process converges to an individually rational allocation
-- statement:
--   Let a job-matching market with at least one firm satisfy regularity of utilities, (MP), (NFL), and (GS) for the discrete market with salary unit $\delta > 0$. Let a run of the salary-adjustment process R1–R5 issue no rejections in round $T$, and let $(\phi; s_{1\phi(1)}(T), \dots, s_{m\phi(m)}(T))$ be the allocation at that round: each worker $i$ goes to the firm $\phi(i)$ whose offer he or she holds, at the permitted salary $s_{i\phi(i)}(T)$. Then this allocation is individually rational:
--
--   $$s_{i\phi(i)}(T) \ge \sigma_{i\phi(i)} \ \text{ for every } i, \qquad \pi^j\big[C^j_\phi; s^j(T)\big] \ge 0 \ \text{ for every } j,$$
--
--   where $C^j_\phi$ is the set of workers assigned to $j$.
--
--   This is Lemma 3 of the paper, the first half of the core property in Lemma 4.
--
--   **Formalization Note** "The process converges to" is read as: at every round $T$ at which no rejections are issued, the allocation read off by R5 has the property. The paper's $t^*$ is such a round.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1489, Lemma 3

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Process_Process

namespace KelsoCrawford.Process

/-- Lemma 3, p. 1489: the allocation at any round where the process stops is individually rational. -/
theorem lemma3_individually_rational
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, GrossSubstitutesOn (M.y j) (M.gridVectors δ j)) :
    ∀ ρ : Run W F, M.IsRun δ ρ → ∀ T : ℕ, ρ.Stopped T → M.IsIR (ρ.outcome T) := by sorry

end KelsoCrawford.Process
