-- Prove2me | Theorems.Thm_LassoDantzig_REConditions_lemma_4_1_i
-- name    : LassoDantzig.REConditions.lemma_4_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T10:26:38.472887+00:00
-- url     : https://prove2.me/theorems/6cd6cd38-deba-4e69-9c30-a135edd3fb9a
-- title:
--   Lemma 4.1 (i) — Assumption 1 implies RE$(s,c_0)$ and RE$(s,s,c_0)$ with constant $\kappa_1(s,c_0)$
-- statement:
--   Let $X\in\mathbb R^{n\times M}$ with $n\ge1$, $M\ge2$. Fix an integer $1\le s\le M/2$ and a constant $c_0>0$, and suppose **Assumption 1** holds:
--
--   $$
--   \phi_{\min}(2s)>c_0\,\theta_{s,2s}.
--   $$
--
--   Then:
--
--   1. $\kappa_1(s,c_0)>0$, and Assumptions RE$(s,c_0)$ and RE$(s,s,c_0)$ hold with $\kappa(s,c_0)\ge\kappa(s,s,c_0)\ge\kappa_1(s,c_0)$.
--   2. For every $J_0$ with $|J_0|\le s$, every $\delta\in\mathbb R^M$ satisfying (4.1) $|\delta_{J_0^c}|_1\le c_0|\delta_{J_0}|_1$, and every choice $J_1$ of the $s$ largest $|\delta_j|$ outside $J_0$,
--   $$
--   \frac1{\sqrt n}\,|P_{01}X\delta|_2\ \ge\ \kappa_1(s,c_0)\,|\delta_{J_{01}}|_2,
--   $$
--   where $J_{01}=J_0\cup J_1$ and $P_{01}$ is the orthogonal projector in $\mathbb R^n$ onto the linear span of the columns of $X_{J_{01}}$.
--
--   With $c_0=1$ Assumption 1 is the condition of Candès and Tao for the Dantzig selector; the lemma shows it yields the RE assumptions for any $c_0>0$.
--
--   **Correction of the printed statement.** The paper writes "hold with $\kappa(s,c_0)=\kappa(s,s,c_0)=\kappa_1(s,c_0)$"; its proof gives $\kappa_1$ as a lower bound, which is what is stated. $P_{01}$ acts on $\mathbb R^n$, not $\mathbb R^M$.
--
--   **Formalization Note** RE through a witness $\kappa$; all admissible $J_1$ under ties; $1\le s\le M/2$ written $1\le s$, $2s\le M$.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 9, Lemma 4.1 (i); proof in Appendix A, p. 20

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- **Lemma 4.1 (i)**, Bickel–Ritov–Tsybakov, arXiv:0801.1095v3, p. 9 (proof: Appendix A,
p. 20). Fix an integer `1 ≤ s ≤ M/2` and `c₀ > 0`, and let Assumption 1 hold. Then
`κ₁(s, c₀) > 0` and it is a valid witness for Assumptions RE(s, c₀) and RE(s, s, c₀) (the paper's
"=" read as "≥", as the proof gives). Moreover, for every `J0` with `|J0| ≤ s`, every `δ`
satisfying (4.1) and every admissible `J1` (the `s` largest `|δ_j|` outside `J0`),
`(1/√n)|P01 X δ|₂ ≥ κ₁(s,c₀)|δ_{J01}|₂`, `P01` the orthogonal projector in `ℝⁿ` onto the span of
the columns of `X_{J01}`, `J01 = J0 ∪ J1`. -/
theorem lemma_4_1_i {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (s : ℕ) (c0 : ℝ) (hs : 1 ≤ s) (hsM : 2 * s ≤ M) (hc0 : 0 < c0)
    (hA1 : Assumption1 X s c0) :
    0 < kappa1 X s c0 ∧
    RE X s c0 (kappa1 X s c0) ∧
    REm X s s c0 (kappa1 X s c0) ∧
    ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, ConeCond c0 J0 δ →
      ∀ J1 : Finset (Fin M), IsTopBlock δ J0 J1 s →
        kappa1 X s c0 * l2On δ (J0 ∪ J1) ≤
          1 / Real.sqrt n * projNorm X (J0 ∪ J1) (X.mulVec δ) := by sorry

end LassoDantzig.REConditions
