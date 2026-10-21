-- Prove2me | Theorems.Thm_HiringLP_SimLower_lemma_10
-- name    : HiringLP.SimLower.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:25.406995+00:00
-- url     : https://prove2.me/theorems/191713d4-871d-4ed8-a894-a69a4597254a
-- title:
--   Lemma 10 — LP_sim(I) ≥ OPT_sim(I)
-- statement:
--   Let $I=(k,n,p,v)$ be a valid Simultaneous Offering instance. Then the LP relaxation is an upper bound on the best expected reward:
--   $$\mathrm{LP}_{\mathrm{sim}}(I)\ \ge\ \mathrm{OPT}_{\mathrm{sim}}(I).$$
--
--   This makes $\mathrm{LP}_{\mathrm{sim}}$ a valid benchmark: a guarantee of the form $R\ge c\,\mathrm{LP}_{\mathrm{sim}}(I)$ is a $c$-approximation of the optimal policy.
--
--   **Formalization Note** $\mathrm{OPT}_{\mathrm{sim}}$ is the maximum over deterministic offer sets of the exact expected reward with overage cost $[|A|-k]^+$.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 27, Lemma 10

import Mathlib
import Definitions.Def_HiringLP_SimLower_Model
import Definitions.Def_HiringLP_SimLower_LP

namespace HiringLP.SimLower

/-- Lemma 10 (p. 27): `LP_sim(I) ≥ OPT_sim(I)` for every instance. -/
theorem lemma_10 {n : ℕ} (I : SimInstance n) (hI : I.Valid) :
    OPTsim I ≤ LPsim I := by sorry

end HiringLP.SimLower
