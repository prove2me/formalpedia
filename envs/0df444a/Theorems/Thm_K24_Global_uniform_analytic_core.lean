-- Prove2me | Theorems.Thm_K24_Global_uniform_analytic_core
-- name    : K24.Global.uniform_analytic_core
-- status  : Open
-- author  : @xwh
-- created : 2026-10-23T19:00:49.462643+00:00
-- url     : https://prove2.me/theorems/3db797ab-2b53-4cda-b318-e4780235e38c
-- title:
--   K24: uniform geometric and analytic estimates before inverse transfer
-- statement:
--   This package defines the remaining geometric and analytic obligations for a proof of the complete conditional K24 theorem. It introduces three transparent conclusion bundles and their uniform statements in the natural Holder, shifted Holder and real-order Sobolev scales.
--
--   Every original non-inverse conclusion is retained: projection laws, exact differential identities, regularity and integrability, actual section-space Banach laws, positive metric neighborhoods, Frechet differentiation, uniform difference and symbol estimates, and center comparison. The original quantifier order is unchanged: numerical geometry/action bounds precede the uniform constants, which then apply to all admissible manifolds, covers, actions and metrics. The Sobolev statement still covers every real $s>4$.
--
--   Four conditional inverse-transfer clauses are removed from these residual bundles. Instead, each bundle explicitly requests that the same actual fixed-reference projected operator maps the specified perpendicular section domain to the specified target and is linear and bounded there. These are unproved conclusions under the unchanged geometric hypotheses. Their finite bounds may depend on the fixed data, including $\lambda$; no new uniform bound by the difference-estimate constants is imposed.
--
--   The conjunction of these three residual uniform statements is `AnalyticCoreStatement`. It is a sufficient residual strengthening, not an asserted equivalence with the original non-inverse clauses. It makes no claim that these obligations are proved. Together with the separate original geometric torus sharpness statement, the proved section Neumann theorem reconstructs the full K24 statement. No target conclusion is inserted as a hypothesis of the original theorem.
--
--   The requested theorem is the full conjunction of those three uniform analytic-core statements. This child remains unproved. Its proof must establish all listed obligations from the original geometry and metric hypotheses. It does not get to assume any of the requested estimates, regularity conclusions or Banach laws. Parent: https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §§2–5 and §8; operator pairs in §3 equations (3.8)–(3.9), §5 equations (5.3)–(5.5); original FullK24Statement definition package https://prove2.me/theorems/9140e2e8-3049-4225-86fe-cfe1a8c49825 .

import Definitions.Def_K24AnalyticCore
set_option autoImplicit false

namespace K24.Global
universe u
theorem uniform_analytic_core : AnalyticCoreStatement.{u} := by sorry
end K24.Global
