-- Prove2me | Theorems.Thm_GRH_smoothed_mobius_character_power_bound
-- name    : GRH.smoothed_mobius_character_power_bound
-- status  : Open
-- author  : @Yi
-- created : 2026-11-20T23:50:56.592914+00:00
-- url     : https://prove2.me/theorems/1a4d349a-86cf-4f83-b726-2459dfb71845
-- title:
--   Square-root cancellation up to $D^\varepsilon$ for exponentially smoothed Dirichlet twists of Möbius
-- statement:
--   For each positive modulus $q$, each Dirichlet character $\chi$ modulo $q$, and each real $1/2<\sigma<1$, establish
--   $$
--   \left|\sum_{n\ge 1}\mu(n)\chi(n)e^{-n/D}\right|=O_{q,\chi,\sigma}(D^\sigma)\qquad(D\to+\infty).
--   $$
--   The scale $D$ is real. The implied constant and the starting scale may depend on the fixed character and exponent. The sum is exponentially smoothed and includes the principal character. This open estimate would yield Dirichlet GRH by Mellin transformation. The cited source provides the conditional analytic passage and uses $23/24$ in its bundled bound. The present $1/2$ threshold is proposed as a new open arithmetic target.
-- source:
--   Proposed threshold 1/2 version of OAI.ShortDraftMellin.ExponentialMobiusPowerBound. For the smoothed sum and the proved Mellin criterion, see LogProfiles.lean, lines 81–169, https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L81-L169

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing

open Filter Asymptotics

theorem GRH.smoothed_mobius_character_power_bound
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    (fun D : ℝ => OAI.ShortDraftMellin.mobiusExpSum χ D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ) := by sorry
