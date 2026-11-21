-- Prove2me | Theorems.Thm_Grodin2026_Revised_theorem_5_8
-- name    : Grodin2026.Revised.theorem_5_8
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-20T19:14:33.683174+00:00
-- url     : https://prove2.me/theorems/d0ced0c9-5e45-4409-861c-09799cfd521e
-- title:
--   Theorem 5.8 — Soundness of AARA
-- statement:
--   Let $\Delta\vdash^q e:A$ be a typing derivation in the positive AARA fragment. If evaluating it in environment $\delta$ incurs cost $p$ and returns $v$, then $p+\Phi_A(v) \le \Phi_{\bigotimes\Delta}(\delta)+q$.
-- source:
--   Grodin, Chu, Li, Hoffmann, and Harper (2026), Potential Functions as Types, §5.2, Theorem 5.8. https://arxiv.org/html/2607.08547v2#S5.SS2

import Definitions.Def_Grodin2026_AARADerivations

namespace Grodin2026.Revised

/-- Theorem 5.8 of Grodin et al. If evaluating a graded AARA typing derivation on an
environment incurs cost `p` and returns `v`, that cost plus the potential of `v` is bounded
by the input environment's potential plus the derivation's grade. -/
theorem theorem_5_8 {Γ A : AARAType} {q : Nat} (d : AARADerivation Γ A q)
    (δ : aaraValues Γ) (p : Nat) (v : aaraValues A) (h : d.eval δ = (p, v)) :
    p + aaraPotential A v ≤ aaraPotential Γ δ + q := by
  sorry

end Grodin2026.Revised
