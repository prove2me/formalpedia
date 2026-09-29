-- Prove2me | Theorems.Thm_LassoDantzig_REConditions_assumption4_implies_RE
-- name    : LassoDantzig.REConditions.assumption4_implies_RE
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T10:38:07.255696+00:00
-- url     : https://prove2.me/theorems/be9f1e3a-203b-4fca-9a42-57c58b42d97d
-- title:
--   (4.2) — Assumption 4 $\phi_{\min}(s)>2c_0\theta_{1,1}s$ implies RE$(s,c_0)$
-- statement:
--   Let $X\in\mathbb R^{n\times M}$ with $n\ge1$, $M\ge2$, let $1\le s\le M$ be an integer and $c_0>0$, and suppose **Assumption 4** holds:
--
--   $$
--   \phi_{\min}(s)>2c_0\,\theta_{1,1}\,s .
--   $$
--
--   Then for every $J_0$ with $|J_0|\le s$ and every $\delta$ satisfying (4.1) $|\delta_{J_0^c}|_1\le c_0|\delta_{J_0}|_1$, the chain (4.2) holds:
--
--   $$
--   \frac1n|X\delta|_2^2\ \ge\ \frac1n\delta_{J_0}^TX^TX\delta_{J_0}-2\theta_{1,1}|\delta_{J_0^c}|_1|\delta_{J_0}|_1
--   \ \ge\ \phi_{\min}(s)|\delta_{J_0}|_2^2-2c_0\theta_{1,1}|\delta_{J_0}|_1^2
--   \ \ge\ \big(\phi_{\min}(s)-2c_0\theta_{1,1}s\big)|\delta_{J_0}|_2^2,
--   $$
--
--   and consequently Assumption RE$(s,c_0)$ holds with the explicit constant $\kappa=\sqrt{\phi_{\min}(s)-2c_0\theta_{1,1}s}>0$.
--
--   Here $\theta_{1,1}=\max_{j\ne k}|x_j^Tx_k|/n$ is a mutual-coherence-type quantity, so Assumption 4 is a coherence condition.
--
--   **Formalization Note** The paper states "Assumption 4 implies RE$(s,c_0)$"; the explicit witness is the one (4.2) produces (a labelled strengthening of the printed claim).
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 10, Section 4, Assumption 4 and Eq. (4.2)

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- **Assumption 4 ⇒ RE(s, c₀)**, with display **(4.2)**, Bickel–Ritov–Tsybakov,
arXiv:0801.1095v3, Section 4, p. 10. If `1 ≤ s ≤ M`, `c₀ > 0` and `φ_min(s) > 2c₀ θ_{1,1} s`
(Assumption 4), then for every `J0` with `|J0| ≤ s` and every `δ` satisfying (4.1),
`(1/n)|Xδ|₂² ≥ (1/n)δ_{J0}ᵀXᵀXδ_{J0} − 2θ_{1,1}|δ_{J0ᶜ}|₁|δ_{J0}|₁
≥ φ_min(s)|δ_{J0}|₂² − 2c₀θ_{1,1}|δ_{J0}|₁² ≥ (φ_min(s) − 2c₀θ_{1,1}s)|δ_{J0}|₂²`, and RE(s, c₀)
holds with the witness `κ = √(φ_min(s) − 2c₀θ_{1,1}s) > 0`. -/
theorem assumption4_implies_RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (s : ℕ) (c0 : ℝ) (hs : 1 ≤ s) (hsM : s ≤ M) (hc0 : 0 < c0)
    (hA4 : 2 * c0 * theta X 1 1 * s < phiMin X s) :
    (∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, ConeCond c0 J0 δ →
      gramQuad X (restrict δ J0) - 2 * theta X 1 1 * l1On δ J0ᶜ * l1On δ J0 ≤ gramQuad X δ ∧
      phiMin X s * l2On δ J0 ^ 2 - 2 * c0 * theta X 1 1 * l1On δ J0 ^ 2 ≤
        gramQuad X (restrict δ J0) - 2 * theta X 1 1 * l1On δ J0ᶜ * l1On δ J0 ∧
      (phiMin X s - 2 * c0 * theta X 1 1 * s) * l2On δ J0 ^ 2 ≤
        phiMin X s * l2On δ J0 ^ 2 - 2 * c0 * theta X 1 1 * l1On δ J0 ^ 2) ∧
    0 < Real.sqrt (phiMin X s - 2 * c0 * theta X 1 1 * s) ∧
    RE X s c0 (Real.sqrt (phiMin X s - 2 * c0 * theta X 1 1 * s)) := by sorry

end LassoDantzig.REConditions
