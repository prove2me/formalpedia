-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_theorem_5_4
-- name    : InfoLossLAR.WorstCase.theorem_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:06:39.122109+00:00
-- url     : https://prove2.me/theorems/f5084a0c-0afa-4c4d-8338-0c14b8cb713a
-- title:
--   Theorem 5.4 — Gaussian LWE to uniform-zero-fiber LWE: $\mathrm{Adv}^{\mathrm{UZF}}_D\le\mathrm{Adv}^{\mathrm{Gauss}}_{B_c}+t\lambda^{-c}$, and the hardness transfer
-- statement:
--   Fix an efficiently computable public parameter family (with Gaussian width $\sigma$ in pp) that admits fixed-order Gaussian T-AFTs (Definition 5.3).
--
--   (1) For every integer $c\ge1$, every uniform QPT distinguisher $D$ on classical sample tables and every positive polynomially bounded block count $t$, there is a uniform QPT reduction $B_c$ that runs $D$ once on a classically prepared table, and a threshold $\lambda_0$, with
--   $$\mathrm{Adv}^{\mathrm{UZF\text{-}LWE}}_D(\lambda,t)\le\mathrm{Adv}^{\mathrm{Gauss\text{-}LWE}}_{B_c}(\lambda,t)+t\lambda^{-c}\qquad(\lambda\ge\lambda_0).$$
--
--   (2) If Gaussian decisional LWE is hard against uniform QPT distinguishers on classical inputs for every positive polynomial block count (the advantage is negligible), then so is uniform-zero-fiber LWE for this family.
--
--   Differences from the source:
--   - reading: "uniform QPT distinguisher/reduction" → `IsQPT` (uniform Clifford+T circuit families on binary-coded inputs); reason: the paper names no model
--   - reading: "uses $t$ input blocks and one call to $D$" → `CallsOnce B D`; reason: structural reading of "one call"
--   - encoding: "polynomially bounded block count" → positive and polynomially bounded; reason: a block count is $\ge1$ (Definition 2.10)
--   - reading: "Gaussian width $\sigma(\lambda)$ included in pp" → a positive rational $\sigma(\lambda)$ in pp; reason: pp is finite binary data
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 24, Theorem 5.4

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_Family

set_option autoImplicit false

open QAlgorithms.Complexity

namespace InfoLossLAR.WorstCase

/-- Theorem 5.4 (Gaussian LWE to uniform-zero-fiber LWE), p. 24, for an efficiently computable
family that admits fixed-order Gaussian T-AFTs. (1) For every integer `c ≥ 1`, every uniform QPT
distinguisher `D` and every positive, polynomially bounded block count `t`, there is a uniform
QPT reduction `B` that runs `D` once on a classically prepared input, and a threshold `λ₀`, with
`Adv^{UZF-LWE}_D(λ, t) ≤ Adv^{Gauss-LWE}_B(λ, t) + t λ^{−c}` for all `λ ≥ λ₀`. (2) If Gaussian
decisional LWE is hard against uniform QPT distinguishers for every positive polynomial block
count, then so is uniform-zero-fiber LWE for this family. -/
theorem theorem_5_4 (F : RoundingFamily) (hF : F.Efficient)
    (hAFT : F.AdmitsFixedOrderGaussianAFT) :
    (∀ c : ℕ, 1 ≤ c → ∀ D : Family, IsQPT D →
      ∀ t : ℕ → ℕ, (∀ lam, 1 ≤ t lam) → PolyBoundedFn t →
        ∃ B : Family, IsQPT B ∧ CallsOnce B D ∧
          ∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
            F.advUZF D lam (t lam) ≤
              F.advGauss B lam (t lam) + (t lam : ℝ) * (lam : ℝ) ^ (-(c : ℝ))) ∧
    ((∀ B : Family, IsQPT B → ∀ t : ℕ → ℕ, (∀ lam, 1 ≤ t lam) → PolyBoundedFn t →
        Negligible fun lam => F.advGauss B lam (t lam)) →
      ∀ D : Family, IsQPT D → ∀ t : ℕ → ℕ, (∀ lam, 1 ≤ t lam) → PolyBoundedFn t →
        Negligible fun lam => F.advUZF D lam (t lam)) := by sorry

end InfoLossLAR.WorstCase
