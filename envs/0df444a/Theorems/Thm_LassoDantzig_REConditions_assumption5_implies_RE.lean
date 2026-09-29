-- Prove2me | Theorems.Thm_LassoDantzig_REConditions_assumption5_implies_RE
-- name    : LassoDantzig.REConditions.assumption5_implies_RE
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T10:41:33.787122+00:00
-- url     : https://prove2.me/theorems/8d5cb641-0f21-4159-a9d2-f0fc6c2ab885
-- title:
--   (4.3) — Assumption 5: unit diagonal and $\theta_{1,1}<1/((1+2c_0)s)$ imply RE$(s,c_0)$
-- statement:
--   Let $X\in\mathbb R^{n\times M}$ with $n\ge1$, $M\ge2$, such that every diagonal entry of the Gram matrix $\Psi_n=X^TX/n$ equals $1$. Let $1\le s\le M$ be an integer and $c_0>0$, and suppose **Assumption 5**, condition (4.3):
--
--   $$
--   \theta_{1,1}<\frac1{(1+2c_0)s}.
--   $$
--
--   Then for every $J_0$ with $|J_0|\le s$ and every $\delta\in\mathbb R^M$,
--
--   $$
--   \frac1n\delta_{J_0}^TX^TX\delta_{J_0}\ \ge\ |\delta_{J_0}|_2^2-\theta_{1,1}|\delta_{J_0}|_1^2\ \ge\ |\delta_{J_0}|_2^2\,(1-\theta_{1,1}s),
--   $$
--
--   and, combining this with (4.2), Assumption RE$(s,c_0)$ holds with the explicit constant $\kappa=\sqrt{1-(1+2c_0)\theta_{1,1}s}>0$.
--
--   With unit diagonal, $\theta_{1,1}$ is the mutual coherence of the design, so (4.3) is a mutual-coherence condition.
--
--   **Formalization Note** The paper states that RE$(s,c_0)$ "is satisfied whenever (4.3) holds"; the explicit witness is the one obtained by combining its display with (4.2) (a labelled strengthening).
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 11, Section 4, Assumption 5 and Eq. (4.3)

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- **Assumption 5 ⇒ RE(s, c₀)**, Bickel–Ritov–Tsybakov, arXiv:0801.1095v3, Section 4, p. 11,
condition (4.3). If every diagonal entry of `Ψ_n = XᵀX/n` equals 1, `1 ≤ s ≤ M`, `c₀ > 0` and
`θ_{1,1} < 1/((1 + 2c₀)s)`, then for every `J0` with `|J0| ≤ s` and every `δ`,
`δ_{J0}ᵀXᵀXδ_{J0}/n ≥ |δ_{J0}|₂² − θ_{1,1}|δ_{J0}|₁² ≥ |δ_{J0}|₂²(1 − θ_{1,1}s)`, and RE(s, c₀)
holds with the witness `κ = √(1 − (1 + 2c₀)θ_{1,1}s) > 0` (obtained by combining this with (4.2)). -/
theorem assumption5_implies_RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (hdiag : ∀ j : Fin M, (1 / (n : ℝ)) * ∑ i, X i j ^ 2 = 1)
    (s : ℕ) (c0 : ℝ) (hs : 1 ≤ s) (hsM : s ≤ M) (hc0 : 0 < c0)
    (hA5 : theta X 1 1 < 1 / ((1 + 2 * c0) * s)) :
    (∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ,
      l2On δ J0 ^ 2 - theta X 1 1 * l1On δ J0 ^ 2 ≤ gramQuad X (restrict δ J0) ∧
      l2On δ J0 ^ 2 * (1 - theta X 1 1 * s) ≤ l2On δ J0 ^ 2 - theta X 1 1 * l1On δ J0 ^ 2) ∧
    0 < Real.sqrt (1 - (1 + 2 * c0) * theta X 1 1 * s) ∧
    RE X s c0 (Real.sqrt (1 - (1 + 2 * c0) * theta X 1 1 * s)) := by sorry

end LassoDantzig.REConditions
