-- Prove2me | Theorems.Thm_KelsoCrawford_Process_lemma4_discrete_core
-- name    : KelsoCrawford.Process.lemma4_discrete_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:46:30.010126+00:00
-- url     : https://prove2.me/theorems/626dd7fe-c6ed-4fb1-a2c1-68de61e0cc49
-- title:
--   Lemma 4 — the process converges to a discrete core allocation in the discrete market for which it is defined
-- statement:
--   Let a job-matching market with at least one firm satisfy regularity of utilities, (MP), (NFL), and (GS) for the discrete market with salary unit $\delta > 0$. Let a run of the salary-adjustment process R1–R5 issue no rejections in round $T$. Then the allocation at round $T$ (each worker at the firm whose offer he or she holds, at its permitted salary) is a **discrete core allocation** (D3) of the discrete market: it is individually rational, pays salaries of the form $\sigma_{ij} + k\delta$, and there are no firm $j$, set of workers $C$ and permitted salaries $r_{ij} \in \{\sigma_{ij} + k\delta : k = 0,1,2,\dots\}$ with
--
--   $$u^i(j; r_{ij}) > u^i\big[\phi(i); s_{i\phi(i)}(T)\big] \ \text{ for all } i \in C, \qquad \pi^j(C; r^j) > \pi^j\big[C^j_\phi; s^j(T)\big].$$
--
--   This is Lemma 4 of the paper, which together with Lemma 2 gives Theorem 1.
--
--   **Formalization Note** Improving coalitions may use only permitted salaries $\sigma_{ij} + k\delta$ with $k \ge 0$ (the paper's "(integer) salaries" in the discrete market whose salaries start at $\sigma_{ij}$). The paper's unit is $1$; for a general unit $\delta$ the statement is the same theorem in rescaled units. The core notion is D3 (both inequalities strict), not the strict core D2.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1490, Lemma 4

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Process_Process

namespace KelsoCrawford.Process

/-- Lemma 4, p. 1490: the allocation at any round where the process stops is a discrete core allocation (D3) of the discrete market with unit δ. -/
theorem lemma4_discrete_core
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, GrossSubstitutesOn (M.y j) (M.gridVectors δ j)) :
    ∀ ρ : Run W F, M.IsRun δ ρ → ∀ T : ℕ, ρ.Stopped T → M.IsCore (M.grid δ) (ρ.outcome T) := by sorry

end KelsoCrawford.Process
