-- Prove2me | Theorems.Thm_Katyusha_NonSC_tau_inequalities
-- name    : Katyusha.NonSC.tau_inequalities
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:35:11.774751+00:00
-- url     : https://prove2.me/theorems/1f8db333-838a-48aa-b9ff-b8ac307da22a
-- title:
--   App. C.1, p. 27 — the parameter inequalities for $\tau_{1,s}=2/(s+4)$
-- statement:
--   Let $\tau_{1,s}=\frac2{s+4}$ for $s=0,1,2,\dots$ and $\tau_2=\frac12$. Then for every $s$,
--   $$\tau_{1,s}\le\frac12,\qquad \frac1{\tau_{1,s}^2}\ge\frac{1-\tau_{1,s+1}}{\tau_{1,s+1}^2},\qquad \frac{\tau_{1,s}+\tau_2}{\tau_{1,s}^2}\ge\frac{\tau_2}{\tau_{1,s+1}^2}.$$
--
--   These are the two inequalities that allow (C.3) and (C.2) to be telescoped over the epochs $s=0,1,\dots,S-1$ into (C.4); the first one guarantees that the parameter choice satisfies the presumptions of Lemma 2.6.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, App. C.1, display after (C.3), p. 27

import Mathlib
import Definitions.Def_Katyusha_NonSC_step

namespace Katyusha.NonSC

/-- The parameter inequalities of Allen-Zhu, arXiv:1603.05953v6, App. C.1, display after (C.3),
p. 27: `τ_{1,s} = 2/(s+4) ≤ 1/2`, and with `τ₂ = 1/2`,
`1/τ_{1,s}² ≥ (1 - τ_{1,s+1})/τ_{1,s+1}²` and `(τ_{1,s} + τ₂)/τ_{1,s}² ≥ τ₂/τ_{1,s+1}²`. -/
theorem tau_inequalities (s : ℕ) :
    tau1 s ≤ 1 / 2 ∧
      1 / tau1 s ^ 2 ≥ (1 - tau1 (s + 1)) / tau1 (s + 1) ^ 2 ∧
      (tau1 s + tau2) / tau1 s ^ 2 ≥ tau2 / tau1 (s + 1) ^ 2 := by sorry

end Katyusha.NonSC
