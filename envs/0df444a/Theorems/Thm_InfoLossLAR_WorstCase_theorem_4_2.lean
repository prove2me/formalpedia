-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_theorem_4_2
-- name    : InfoLossLAR.WorstCase.theorem_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:06:29.200338+00:00
-- url     : https://prove2.me/theorems/bda9fef1-8ac2-4713-a431-37eb06cb3c8e
-- title:
--   Theorem 4.2 — uniform-zero-fiber LWE to decisional LAR: $\mathrm{Adv}^{\mathrm{dLAR}}_D\le q\,\mathrm{Adv}^{\mathrm{LWE}}_B+q^{-N}$
-- statement:
--   Fix an efficiently computable public parameter family as in §3.1 and the error law $\chi=U(\mathcal F_{T,0})$. For every uniform QPT distinguisher $D$ on classical sample tables and every positive integer-valued sample count $t(\lambda)$ bounded by a polynomial, there is a uniform QPT distinguisher $B$, which runs $D$ once on a classically prepared table, such that for every security parameter $\lambda\ge1$
--   $$\mathrm{Adv}^{\mathrm{dLAR}}_D(\lambda,t(\lambda))\le q\,\mathrm{Adv}^{\mathrm{LWE}}_B(\lambda,t(\lambda))+q^{-N}.$$
--   Here $B$ receives $t(\lambda)$ LWE blocks $(A_i,b_i)$ with $\chi=U(\mathcal F_{T,0})$.
--
--   This is the first of the two classical reductions from Gaussian LWE to decisional LAR.
--
--   Differences from the source:
--   - reading: "uniform QPT distinguisher" → a uniform, well-formed, polynomially bounded Clifford+T circuit family on the binary code of $(1^\lambda,\mathrm{pp},\text{table})$; reason: the paper names no model
--   - reading: "using $t$ input blocks and one call to $D$" → `CallsOnce B D`: $\Pr[B(w)=1]$ equals running $D$ once on a classical polynomial-time preprocessing of $(w,\text{coins})$ followed by a classical polynomial-time post-processing of its bit; reason: structural reading of "one call"
--   - encoding: pp of a §3.1 family → also lists a rational width $\sigma>0$ (Definition 5.3's augmentation); reason: one family type serves §§3–5; an extra public entry changes no instance
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 22, Theorem 4.2

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_Family

set_option autoImplicit false

open QAlgorithms.Complexity

namespace InfoLossLAR.WorstCase

/-- Theorem 4.2 (From uniform-zero-fiber LWE to decisional LAR), p. 22: for an efficiently
computable public parameter family and `χ = U(F_{T,0})`, for every uniform QPT distinguisher `D`
and every positive, polynomially bounded sample count `t`, there is a uniform QPT distinguisher
`B` that runs `D` once on a classically prepared input, with
`Adv^{dLAR}_D(λ, t) ≤ q · Adv^{LWE}_B(λ, t) + q^{−N}` for every `λ ≥ 1`. -/
theorem theorem_4_2 (F : RoundingFamily) (hF : F.Efficient) (D : Family) (hD : IsQPT D)
    (t : ℕ → ℕ) (ht : ∀ lam, 1 ≤ t lam) (htp : PolyBoundedFn t) :
    ∃ B : Family, IsQPT B ∧ CallsOnce B D ∧
      ∀ lam : ℕ, 1 ≤ lam →
        F.advLAR D lam (t lam) ≤
          (F.q lam : ℝ) * F.advUZF B lam (t lam) + ((F.q lam : ℝ) ^ F.N lam)⁻¹ := by sorry

end InfoLossLAR.WorstCase
