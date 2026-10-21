-- Prove2me | Theorems.Thm_IdentityMgmt_FIA_corollary_1
-- name    : IdentityMgmt.FIA.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:52.524118+00:00
-- url     : https://prove2.me/theorems/96dd6ea1-d19a-4a30-8f73-801512d9afe9
-- title:
--   Corollary 1, pp. 26–27 (PDF 30–31) — the unserved fraction θ_inf = K/(1−γ) decreases in θ̃ and is zero at θ̃ = 1
-- statement:
--   In the FIA identity-management game, let $\theta_{\inf} = K/(1-\gamma)$ be the limit of the market-expansion path $\theta_{n+1} = K + \gamma\theta_n$: types below $\theta_{\inf}$ are never served.
--
--   1. If two quasi-linear Markov equilibria have the same discount factor and pivots $\tilde\theta_P < \tilde\theta_Q$, then $\theta_{\inf, Q} < \theta_{\inf, P}$: the unserved fraction is a strictly decreasing function of $\tilde\theta$.
--   2. In every Markov equilibrium with $\tilde\theta = 1$ (no active customers), $\theta_{\inf} = 0$.
--
--   Hence the market is eventually fully covered when nobody manages her identity.
--
--   **Formalization Note.** Only the second and third sentences of Corollary 1 are formalized; the first ($\gamma^*$ decreasing in $\beta$, $\gamma^* = 1/2$ at $\beta = 0$) is argued in the paper from the printed (29), which does not follow from the model.
-- source:
--   Laussel, Long & Resende, Profit Effects of Consumers' Identity Management: A Dynamic Model, CIRANO working paper 2021s-29 (24 Aug. 2021), pp. 26–27 (PDF 30–31), Corollary 1, second and third sentences

import Mathlib
import Definitions.Def_IdentityMgmt_FIA_Model

namespace IdentityMgmt.FIA

theorem corollary_1 :
    (∀ P Q : Profile, P.IsMarkovEq → Q.IsMarkovEq → P.β = Q.β → P.θt < Q.θt →
      Q.θinf < P.θinf) ∧
    (∀ P : Profile, P.IsMarkovEq → P.θt = 1 → P.θinf = 0) := by sorry

end IdentityMgmt.FIA
