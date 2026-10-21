-- Prove2me | Theorems.Thm_IdentityMgmt_FIA_psi_limit
-- name    : IdentityMgmt.FIA.psi_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:05.937986+00:00
-- url     : https://prove2.me/theorems/3bddb41c-5af8-4435-8ef2-420ca5235388
-- title:
--   Proof of Proposition 1, OA p. 5 (PDF 59) — in an FIA Markov equilibrium, Ψ(θ_n) → 0 along the expansion path
-- statement:
--   In every quasi-linear FIA Markov equilibrium (cut-off rule $\theta_{n+1} = K + \gamma\theta_n$ from $\theta_0 = \tilde\theta$, expectations rule $\Psi(\theta) = C + \lambda\theta$),
--   $$\lim_{n\to\infty} \Psi(\theta_n) = 0.$$
--
--   $\Psi(\theta_n)$ is the lifetime net utility of the period-$n$ marginal passive customer, so the limit says that the last type to be served, $\theta_{\inf}$, gets zero surplus. This is the boundary condition (14), which the paper first imposes as an expectation; here it is derived from the arbitrage equation.
-- source:
--   Laussel, Long & Resende, Profit Effects of Consumers' Identity Management: A Dynamic Model, CIRANO working paper 2021s-29 (24 Aug. 2021), Online Appendix, OA p. 5 (PDF 59), proof of Proposition 1, last display; cf. p. 24 (PDF 28), eq. (14)

import Mathlib
import Definitions.Def_IdentityMgmt_FIA_Model

namespace IdentityMgmt.FIA

theorem psi_limit (P : Profile) (hP : P.IsMarkovEq) :
    Filter.Tendsto (fun n => P.Ψ (P.path n)) Filter.atTop (nhds 0) := by sorry

end IdentityMgmt.FIA
