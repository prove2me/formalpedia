-- Prove2me | Theorems.Thm_ImpactCopula_lemma_1
-- name    : ImpactCopula.lemma_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:53:45.557881+00:00
-- url     : https://prove2.me/theorems/acd9b0d7-3645-4349-9514-8152d75f98cb
-- title:
--   Lemma 1 — the partial Dini derivatives of a copula are non-decreasing in $v$
-- statement:
--   Let $C$ be a copula and $u \in (0,1)$. Then the partial right and left upper Dini derivatives
--
--   $$
--   D_1^+C(u,v) = \limsup_{h\to0^+}\frac{C(u+h,v)-C(u,v)}{h}, \qquad D_1^-C(u,v) = \limsup_{h\to0^+}\frac{C(u,v)-C(u-h,v)}{h}
--   $$
--
--   are non-decreasing functions of $v \in [0,1]$.
--
--   This monotonicity is what makes the infimum in the definition (A.30) of the modified partial Dini derivative a right limit, so that $D_1C(u,\cdot)$ is a distribution function.
--
--   Differences from the source:
--   - encoding: "non-decreasing with respect to v", copula on $[0,1]^2$ → monotone on $v \in [0,1]$, $C$ a function on $\mathbb R^2$ satisfying `coIsCopula` on $[0,1]^2$, limsup as real `Filter.limsup`; reason: $[0,1]$ is the copula's domain in $v$; the quotients are bounded for small $h$, so the real limsup is the true one.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Lemma 1, p.75 (PDF p.78)

import Mathlib
import Definitions.Def_actuarial_coIsCopula
import Definitions.Def_ImpactCopula_diniRightUpper
import Definitions.Def_ImpactCopula_diniLeftUpper

namespace ImpactCopula

/-- **Lemma 1**, Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.75 (PDF p.78): "Let C(u, v) be a copula. Then, the partial Dini
derivatives D₁⁺C(u, v) and D₁⁻C(u, v) defined by (A.31) are non-decreasing with respect to v for
any u ∈ (0, 1)."

**Formalization Note.** "Non-decreasing with respect to v" is monotonicity on `[0, 1]`, the
copula's domain in `v` (`C` is a function on `ℝ²` constrained by `coIsCopula` on `[0, 1]²`).
The Dini derivatives are real `limsup`s, which are the true ones because the difference quotients
lie in `[0, 1]` for small `h > 0`. -/
theorem lemma_1 (C : ℝ → ℝ → ℝ) (hC : ActuarialValuation.coIsCopula C) (u : ℝ)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    MonotoneOn (fun v => diniRightUpper C u v) (Set.Icc 0 1) ∧
      MonotoneOn (fun v => diniLeftUpper C u v) (Set.Icc 0 1) := by sorry

end ImpactCopula
