-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_law_comp_affine_readable
-- name    : FunctionalInequalities.KLS.RegularPotential.law_comp_affine_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:10.922633+00:00
-- url     : https://prove2.me/theorems/a3faf409-b5c0-4734-ac62-cbff615f4315
-- title:
--   Affine Transformation Rule for Regular Potential Laws
-- statement:
--   This formalizes the affine stability statement for regular log-concave measures in Section 2, equation (12), of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a finite-dimensional complete real inner-product space with its Borel measurable structure. Let $V:E\to\mathbb R$ and suppose `RegularPotential V a b` holds for real constants $a,b$. Let $L:E\simeq_L E$ be a continuous linear equivalence and let $c\in E$. The law `RegularPotential.comp_affine hV L c` of the potential $x\mapsto V(Lx+c)$ is the pushforward of the original law under $y\mapsto L^{-1}(y-c)$:
--
--   $$
--   \operatorname{law}(V\circ(L\,\cdot+c))
--   =
--   \operatorname{map}\bigl(y\mapsto L^{-1}(y-c)\bigr)\bigl(\operatorname{law}(V)\bigr).
--   $$
--
--   The result is a reusable change-of-variables identity for centering and affine normalization of regular laws.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem RegularPotential.law_comp_affine
--       (L : E ≃L[ℝ] E) (c : E) :
--       ((RegularPotential.comp_affine hV L c).law : Measure E) =
--         (hV.law : Measure E).map (fun y => L.symm (y - c))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Regular/Affine`](https://prove2.me/theorems/29516924-6815-4c08-8c28-b0309812c8d6).
--
--   Definition modules: [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342).
--
--   Supporting theorems: [`Probability.tilted_smul_pos`](https://prove2.me/theorems/082bb7e7-9916-4a6e-aaa8-68ce8d9f378f).
--
--   [Source excerpt, lines 71–74](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Regular/Affine.lean#L71-L74) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Section 2, (12), p. 5 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Regular/Affine.lean#L68-L88 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Regular.Affine`, declaration `FunctionalInequalities.KLS.RegularPotential.law_comp_affine`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Affine

open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {V : E → ℝ} {a b : ℝ} (hV : FunctionalInequalities.KLS.RegularPotential V a b)
include hV

theorem FunctionalInequalities.KLS.RegularPotential.law_comp_affine_readable
    (L : E ≃L[ℝ] E) (c : E) :
    ((RegularPotential.comp_affine hV L c).law : Measure E) =
      (hV.law : Measure E).map (fun y => L.symm (y - c)) := by sorry
