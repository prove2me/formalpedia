-- Prove2me | Theorems.Thm_LassoDantzig_REConditions_lemma_4_1_ii
-- name    : LassoDantzig.REConditions.lemma_4_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T10:18:56.759206+00:00
-- url     : https://prove2.me/theorems/b8c2c600-865a-4265-be9f-f4883a9c5c30
-- title:
--   Lemma 4.1 (ii) — Assumption 2 implies RE$(s,c_0)$ and RE$(s,m,c_0)$ with constant $\kappa_2(s,m,c_0)$
-- statement:
--   Let $X\in\mathbb R^{n\times M}$ with $n\ge1$, $M\ge2$. Fix integers $s,m$ with $1\le s\le M/2$, $m\ge s$, $s+m\le M$, and a constant $c_0>0$, and suppose **Assumption 2** holds:
--
--   $$
--   m\,\phi_{\min}(s+m)>c_0^2\,s\,\phi_{\max}(m).
--   $$
--
--   Then:
--
--   1. $\kappa_2(s,m,c_0)>0$, and Assumptions RE$(s,c_0)$ and RE$(s,m,c_0)$ hold with $\kappa(s,c_0)\ge\kappa(s,m,c_0)\ge\kappa_2(s,m,c_0)$; that is, for every $J_0$ with $|J_0|\le s$, every $\delta\neq0$ with $|\delta_{J_0^c}|_1\le c_0|\delta_{J_0}|_1$ and every choice $J_1$ of the $m$ largest $|\delta_j|$ outside $J_0$,
--   $$
--   |X\delta|_2\ge\kappa_2(s,m,c_0)\sqrt n\,|\delta_{J_{01}}|_2\ge\kappa_2(s,m,c_0)\sqrt n\,|\delta_{J_0}|_2,\qquad J_{01}=J_0\cup J_1 .
--   $$
--   2. For every $J_0$ with $|J_0|\le s$, every $\delta\in\mathbb R^M$ satisfying (4.1) and every such $J_1$,
--   $$
--   \frac1{\sqrt n}\,|P_{01}X\delta|_2\ \ge\ \kappa_2(s,m,c_0)\,|\delta_{J_{01}}|_2,
--   $$
--   where $P_{01}$ is the orthogonal projector in $\mathbb R^n$ onto the linear span of the columns of $X_{J_{01}}$.
--
--   The lemma turns a condition on the extreme eigenvalues of small principal submatrices of the Gram matrix into the restricted eigenvalue condition on which all of the paper's Lasso and Dantzig selector bounds rest.
--
--   **Correction of the printed statement.** The paper writes "hold with $\kappa(s,c_0)=\kappa(s,m,c_0)=\kappa_2(s,m,c_0)$". Equality is false in general; its proof (p. 20) gives the lower bound, i.e. $\kappa_2$ is a valid RE constant, and that is what is stated. The paper also calls $P_{01}$ "the projector in $\mathbb R^M$"; it acts on $\mathbb R^n$.
--
--   **Formalization Note** RE is formalized through a witness $\kappa$ (see the definition `RE`); the statement asserts that $\kappa_2(s,m,c_0)$ is a positive witness for both assumptions. Under ties all admissible $J_1$ are covered. $1\le s\le M/2$ is written $1\le s$, $2s\le M$.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 9, Lemma 4.1 (ii); proof in Appendix A, pp. 19–20

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- **Lemma 4.1 (ii)**, Bickel–Ritov–Tsybakov, arXiv:0801.1095v3, p. 9 (proof: Appendix A,
pp. 19–20). Fix integers `1 ≤ s ≤ M/2`, `m ≥ s`, `s + m ≤ M` and `c₀ > 0`, and let Assumption 2
hold. Then `κ₂(s, m, c₀) > 0` and it is a valid witness for Assumptions RE(s, c₀) and
RE(s, m, c₀) (the paper's "hold with κ(s,c₀) = κ(s,m,c₀) = κ₂(s,m,c₀)" read as
`κ(s,c₀) ≥ κ(s,m,c₀) ≥ κ₂(s,m,c₀)`, which is what the proof gives). Moreover, for every `J0`
with `|J0| ≤ s`, every `δ` satisfying (4.1) and every admissible `J1` (the `m` largest `|δ_j|`
outside `J0`), `(1/√n)|P01 X δ|₂ ≥ κ₂(s,m,c₀)|δ_{J01}|₂`, with `P01` the orthogonal projector in
`ℝⁿ` onto the span of the columns of `X_{J01}`, `J01 = J0 ∪ J1`. -/
theorem lemma_4_1_ii {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (s m : ℕ) (c0 : ℝ) (hs : 1 ≤ s) (hsM : 2 * s ≤ M) (hms : s ≤ m) (hsmM : s + m ≤ M)
    (hc0 : 0 < c0) (hA2 : Assumption2 X s m c0) :
    0 < kappa2 X s m c0 ∧
    RE X s c0 (kappa2 X s m c0) ∧
    REm X s m c0 (kappa2 X s m c0) ∧
    ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, ConeCond c0 J0 δ →
      ∀ J1 : Finset (Fin M), IsTopBlock δ J0 J1 m →
        kappa2 X s m c0 * l2On δ (J0 ∪ J1) ≤
          1 / Real.sqrt n * projNorm X (J0 ∪ J1) (X.mulVec δ) := by sorry

end LassoDantzig.REConditions
