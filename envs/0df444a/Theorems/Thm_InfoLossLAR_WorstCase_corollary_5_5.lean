-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_corollary_5_5
-- name    : InfoLossLAR.WorstCase.corollary_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:07:05.849346+00:00
-- url     : https://prove2.me/theorems/c6bea6df-6d4d-4436-af17-35030e6c9045
-- title:
--   Corollary 5.5 — Gaussian LWE to decisional LAR: $\mathrm{Adv}^{\mathrm{dLAR}}_D\le q\,\mathrm{Adv}^{\mathrm{Gauss}}_{B_c}+qt\lambda^{-c}+q^{-N}$, and the hardness transfer
-- statement:
--   Under the hypotheses of Theorem 5.4 (an efficiently computable family admitting fixed-order Gaussian T-AFTs):
--
--   (1) for every integer $c\ge1$, every positive polynomially bounded $t$ and every uniform QPT distinguisher $D$ there is a uniform QPT reduction $B_c$, running $D$ once on a classically prepared table, such that for all sufficiently large $\lambda$
--   $$\mathrm{Adv}^{\mathrm{dLAR}}_D(\lambda,t)\le q\,\mathrm{Adv}^{\mathrm{Gauss\text{-}LWE}}_{B_c}(\lambda,t)+qt\lambda^{-c}+q^{-N};$$
--
--   (2) if $q$ is polynomially bounded, $q^{-N}$ is negligible, and Gaussian decisional LWE is hard against uniform QPT distinguishers on classical inputs for every positive polynomial block count, then decisional LAR is hard against such distinguishers for every positive polynomial sample count, for the same family.
--
--   Differences from the source:
--   - reading: "uniform QPT distinguisher/reduction" → `IsQPT`; reason: the paper names no model
--   - reading: "uses $t$ source blocks and invokes $D$ once" → `CallsOnce B D`; reason: structural reading of "one call"
--   - encoding: "polynomially bounded $t$" / "polynomial sample count" → positive and polynomially bounded; reason: sample and block counts are $\ge1$ (Definitions 2.10, 3.6)
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 25, Corollary 5.5

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_Family

set_option autoImplicit false

open QAlgorithms.Complexity

namespace InfoLossLAR.WorstCase

/-- Corollary 5.5 (Gaussian LWE to decisional LAR), p. 25, under the hypotheses of Theorem 5.4.
(1) For every integer `c ≥ 1`, every positive polynomially bounded `t` and every uniform QPT `D`
there is a uniform QPT reduction `B` running `D` once on a classically prepared input, with
`Adv^{dLAR}_D(λ, t) ≤ q Adv^{Gauss-LWE}_B(λ, t) + q t λ^{−c} + q^{−N}` for all large `λ`.
(2) If `q` is polynomially bounded, `q^{−N}` is negligible, and Gaussian decisional LWE is hard
against uniform QPT distinguishers for every positive polynomial block count, then decisional
LAR is hard against uniform QPT distinguishers for every positive polynomial sample count. -/
theorem corollary_5_5 (F : RoundingFamily) (hF : F.Efficient)
    (hAFT : F.AdmitsFixedOrderGaussianAFT) :
    (∀ c : ℕ, 1 ≤ c → ∀ t : ℕ → ℕ, (∀ lam, 1 ≤ t lam) → PolyBoundedFn t →
      ∀ D : Family, IsQPT D →
        ∃ B : Family, IsQPT B ∧ CallsOnce B D ∧
          ∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
            F.advLAR D lam (t lam) ≤
              (F.q lam : ℝ) * F.advGauss B lam (t lam) +
                (F.q lam : ℝ) * (t lam : ℝ) * (lam : ℝ) ^ (-(c : ℝ)) +
                ((F.q lam : ℝ) ^ F.N lam)⁻¹) ∧
    ((PolyBoundedFn F.q ∧ Negligible (fun lam => ((F.q lam : ℝ) ^ F.N lam)⁻¹) ∧
        ∀ B : Family, IsQPT B → ∀ t : ℕ → ℕ, (∀ lam, 1 ≤ t lam) → PolyBoundedFn t →
          Negligible fun lam => F.advGauss B lam (t lam)) →
      ∀ D : Family, IsQPT D → ∀ t : ℕ → ℕ, (∀ lam, 1 ≤ t lam) → PolyBoundedFn t →
        Negligible fun lam => F.advLAR D lam (t lam)) := by sorry

end InfoLossLAR.WorstCase
