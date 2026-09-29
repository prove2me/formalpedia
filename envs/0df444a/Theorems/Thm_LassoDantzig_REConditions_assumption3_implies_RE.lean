-- Prove2me | Theorems.Thm_LassoDantzig_REConditions_assumption3_implies_RE
-- name    : LassoDantzig.REConditions.assumption3_implies_RE
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T10:30:20.869251+00:00
-- url     : https://prove2.me/theorems/62c5d5b1-daa8-425e-b3ed-79500b5498a7
-- title:
--   Assumption 3 $\phi_{\min}(s)>2c_0\theta_{s,1}\sqrt s$ implies RE$(s,c_0)$
-- statement:
--   Let $X\in\mathbb R^{n\times M}$ with $n\ge1$, $M\ge2$, let $1\le s\le M$ be an integer and $c_0>0$, and suppose **Assumption 3** holds:
--
--   $$
--   \phi_{\min}(s)>2c_0\,\theta_{s,1}\sqrt s .
--   $$
--
--   Then Assumption RE$(s,c_0)$ holds, with the explicit constant $\kappa=\sqrt{\phi_{\min}(s)-2c_0\theta_{s,1}\sqrt s}>0$: for every $J_0$ with $|J_0|\le s$ and every $\delta\ne0$ with $|\delta_{J_0^c}|_1\le c_0|\delta_{J_0}|_1$,
--
--   $$
--   \frac1n|X\delta|_2^2\ \ge\ \big(\phi_{\min}(s)-2c_0\theta_{s,1}\sqrt s\big)\,|\delta_{J_0}|_2^2 .
--   $$
--
--   This is one of three sufficient conditions for RE$(s,c_0)$ discussed in Section 4 of the paper, attributed there to reference [1].
--
--   **Formalization Note** The paper states only "Assumption 3 implies RE$(s,c_0)$"; the explicit witness is the one produced by the displayed argument on p. 10 and is a (labelled) strengthening of the printed claim.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 10, Section 4, Assumption 3 ⇒ RE(s, c0)

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- **Assumption 3 ⇒ RE(s, c₀)**, Bickel–Ritov–Tsybakov, arXiv:0801.1095v3, Section 4, p. 10.
If `1 ≤ s ≤ M`, `c₀ > 0` and `φ_min(s) > 2c₀ θ_{s,1} √s` (Assumption 3), then RE(s, c₀) holds
with the explicit witness `κ = √(φ_min(s) − 2c₀ θ_{s,1} √s) > 0` given by the displayed argument. -/
theorem assumption3_implies_RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (s : ℕ) (c0 : ℝ) (hs : 1 ≤ s) (hsM : s ≤ M) (hc0 : 0 < c0)
    (hA3 : 2 * c0 * theta X s 1 * Real.sqrt s < phiMin X s) :
    0 < Real.sqrt (phiMin X s - 2 * c0 * theta X s 1 * Real.sqrt s) ∧
    RE X s c0 (Real.sqrt (phiMin X s - 2 * c0 * theta X s 1 * Real.sqrt s)) := by sorry

end LassoDantzig.REConditions
