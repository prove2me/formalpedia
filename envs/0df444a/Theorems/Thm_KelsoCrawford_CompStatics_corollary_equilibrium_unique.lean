-- Prove2me | Theorems.Thm_KelsoCrawford_CompStatics_corollary_equilibrium_unique
-- name    : KelsoCrawford.CompStatics.corollary_equilibrium_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:53.08748+00:00
-- url     : https://prove2.me/theorems/e1c85e7a-ca70-4098-979e-54073c423d38
-- title:
--   Corollary to Theorem 4 — unique salary-adjustment equilibrium
-- statement:
--   Consider a finite discrete job-matching market with a positive salary increment $\delta$, regular worker utilities, marginal product (MP), no free lunch (NFL), gross substitutes on the salary grid, and the no-ties conditions (NTW) and (NTF). For any two legal salary-adjustment runs $\rho,\rho'$ and stopping rounds $T,T'$, the resulting allocations agree:
--
--   $$A_{\rho,T}=A_{\rho',T'}.$$
--
--   Thus the process equilibrium is independent of firms' and workers' permitted tie choices and of the stopping round.
--
--   **Formalization Note** This gives uniqueness conditional on two runs and their stopping rounds. Existence and finite stopping are the preceding Theorem 1 and Theorem 4 results. The regularity, MP, NFL, and grid-GS assumptions are inherited from the paper's standing market assumptions.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1496, Corollary to Theorem 4; standing assumptions p. 1486. https://doi.org/10.2307/1913392

import Mathlib
import Definitions.Def_KelsoCrawford_CompStatics_Process

namespace KelsoCrawford.CompStatics

theorem corollary_equilibrium_unique
    {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ)
    (hδ : 0 < δ) (hM : M.Theorem4Conditions δ)
    (ρ ρ' : Run W F)
    (hρ : M.IsRun δ ρ) (hρ' : M.IsRun δ ρ')
    (T T' : ℕ) (hT : ρ.Stopped T) (hT' : ρ'.Stopped T') :
    ρ.outcome T = ρ'.outcome T' := by sorry

end KelsoCrawford.CompStatics
