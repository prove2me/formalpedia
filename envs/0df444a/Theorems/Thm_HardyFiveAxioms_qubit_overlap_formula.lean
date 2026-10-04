-- Prove2me | Theorems.Thm_HardyFiveAxioms_qubit_overlap_formula
-- name    : HardyFiveAxioms.qubit_overlap_formula
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T22:45:44.072919+00:00
-- url     : https://prove2.me/theorems/cf177f8f-1817-47db-b233-63fc4b624e87
-- title:
--   Qubit overlap: $c=1-a-b+2ab+2\cos(\phi_4-\phi_3)\sqrt{ab(1-a)(1-b)}$
-- statement:
--   Let $0\le a,b\le1$ and $\phi_3,\phi_4\in\mathbb R$. Put
--
--   $$\alpha=\sqrt{1-a},\quad\beta=\sqrt a\,e^{i\phi_3},\quad\gamma=\sqrt{1-b},\quad\delta=\sqrt b\,e^{i\phi_4},$$
--
--   and let $\hat P_3=(\alpha|1\rangle+\beta|2\rangle)(\alpha^*\langle1|+\beta^*\langle2|)$ and $\hat P_4=(\gamma|1\rangle+\delta|2\rangle)(\gamma^*\langle1|+\delta^*\langle2|)$, as in Eqs. (31)–(32). Then the entry $c=D_{34}=\mathrm{tr}(\hat P_3\hat P_4)=|\alpha\gamma^*+\beta\delta^*|^2$ equals
--
--   $$c=1-a-b+2ab+2\cos(\phi_4-\phi_3)\sqrt{ab(1-a)(1-b)} .$$
--
--   This is Eq. (35). Varying the phases yields $c_-\le c\le c_+$.
--
--   **Formalization Note** The paper says $\alpha$ and $\gamma$ "can be chosen real". The statement takes the nonnegative real choice $\alpha=\sqrt{1-a}$, $\gamma=\sqrt{1-b}$. The paper's $\delta=\sqrt b\exp(\phi_4)$ is read as $\sqrt b\,e^{i\phi_4}$, an evident typo. The trace is computed in Lean for $\mathrm{proj}(v)=|v\rangle\langle v|$.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 9, Section 5, Eqs. (31)–(35)

import Mathlib
import Definitions.Def_hardy2001_projectors

namespace HardyFiveAxioms

/-- Hardy 2001, Section 5, Eqs. (31)–(35): with `α = √(1-a)`, `β = √a e^{iφ₃}`,
`γ = √(1-b)`, `δ = √b e^{iφ₄}`, the entry `c = tr(P̂₃P̂₄) = |αγ* + βδ*|²` of `D` equals
`1 - a - b + 2ab + 2 cos(φ₄ - φ₃) √(ab(1-a)(1-b))`. -/
theorem qubit_overlap_formula (a b φ₃ φ₄ : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    (proj ![(Real.sqrt (1 - a) : ℂ), (Real.sqrt a : ℂ) * Complex.exp (φ₃ * Complex.I)] *
        proj ![(Real.sqrt (1 - b) : ℂ), (Real.sqrt b : ℂ) * Complex.exp (φ₄ * Complex.I)]).trace =
      ((1 - a - b + 2 * a * b + 2 * Real.cos (φ₄ - φ₃) * Real.sqrt (a * b * (1 - a) * (1 - b)) :
        ℝ) : ℂ) := by sorry

end HardyFiveAxioms
