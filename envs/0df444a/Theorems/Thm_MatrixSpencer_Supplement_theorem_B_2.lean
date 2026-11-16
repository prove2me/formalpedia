-- Prove2me | Theorems.Thm_MatrixSpencer_Supplement_theorem_B_2
-- name    : MatrixSpencer.Supplement.theorem_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:30:32.933974+00:00
-- url     : https://prove2.me/theorems/527c9355-3feb-4d55-be4c-e59316977945
-- title:
--   Theorem B.2 — one rank-one pinching costs at most $c_{\mathrm{Schur}}$, independently of the dimension
-- statement:
--   Let $A_1,\dots,A_n$ be symmetric $d\times d$ matrices with
--   $$\sum_{i=1}^n A_i^2\preceq I_d .$$
--   Fix a unit vector $v\in\mathbb R^d$ and decompose each $A_i$ with respect to $\mathbb R^d=\mathrm{span}\{v\}\oplus v^\perp$ as $A_i=\begin{pmatrix}a_i&u_i^\top\\u_i&D_i\end{pmatrix}$. For $g\in\mathbb R^n$ let $a(g)=\frac14\sum_ig_ia_i$, $b(g)=\frac14\sum_ig_iu_i$, $C(g)=\frac14\sum_ig_iD_i$, let $\Omega_0=\{g:|a(g)|<1,\ \|C(g)\|_{\mathrm{op}}<1\}$, and consider the tilted Gaussian measure
--   $$d\mu_0(g)=\frac{w_0(g)}{\mathbb E w_0}\,d\gamma_n(g),\qquad w_0(g)=(1-a(g)^2)^4\det(I_{d-1}-C(g)^2)^4\,\mathbf 1_{\Omega_0}(g),$$
--   where $\gamma_n$ is the standard Gaussian measure on $\mathbb R^n$. With the Schur terms $\xi_\pm$ of (B.14) on $\Omega_0$,
--   $$\mathbb E_{\mu_0}(1-\xi_+)_+^4(1-\xi_-)_+^4\ \ge\ c_{\mathrm{Schur}}=\Bigl[1-\tfrac18(\Lambda^2+\Lambda^{-2})\Bigr]^8,\qquad \Lambda=8-4\sqrt3 .$$
--
--   The left side is the ratio of the log-barrier partition function of the full matrix to that of its pinching $a\oplus C$. Iterating the bound along $d-1$ rank-one pinchings reduces the matrix small-ball problem to a diagonal one (Theorem 1.5), losing only a factor $c_{\mathrm{Schur}}$ per step.
--
--   **Formalization Note** The dimension is $d=m+1$, and the splitting is given by an orthogonal matrix $Q$ whose first column is $v$; the statement is asserted for every such $Q$. The expectation under $\mu_0$ is written as $\int F\,w_0\,d\gamma_n\big/\int w_0\,d\gamma_n$, and $(t)_+=\max(t,0)$.
--
--   Differences from the source:
--   - encoding: a unit vector v ∈ ℝᵈ and the block decomposition w.r.t. span{v} ⊕ v^⊥ → d = m + 1, an orthogonal matrix Q with column 0 equal to v, and the blocks of Qᵀ Aᵢ Q (v is then a unit vector); reason: d ≥ 1 is forced by the existence of a unit vector, and the left side does not depend on the orthonormal basis of v^⊥, so quantifying over every Q is the page's statement
--   - encoding: E_{µ₀} with dµ₀ = (w₀/Ew₀) dγₙ, (t)₊ → (∫ F w₀ dγₙ)/(∫ w₀ dγₙ), max t 0; reason: definition of the normalized measure; the integrands are bounded and measurable, so no Bochner default value enters
--   - encoding: ξ± defined for g ∈ Ω₀ only → ξ± total functions with Lean's default inverse and division off Ω₀; reason: they are multiplied by w₀ = 0 off Ω₀, so the integrand is unchanged
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem B.2, pp.17–18 (PDF pp.19–20), eqs. (B.14)–(B.16)

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_MatrixSpencer_gam
import Definitions.Def_MatrixSpencer_Supplement_pinMat
import Definitions.Def_MatrixSpencer_Supplement_w0
import Definitions.Def_MatrixSpencer_Supplement_cSchur
open RBMSensitivity (E)

namespace MatrixSpencer.Supplement

/-- **Theorem B.2 (Dimension-free lower bounds on ratio of partition functions).**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…),
Theorem B.2, pp.17–18 (PDF pp.19–20): for symmetric `A₁, …, Aₙ` with `∑ᵢ Aᵢ² ⪯ I_d`, a unit vector
`v`, and the blocks, weight `w₀`, set `Ω₀` and Schur terms `ξ±` of the page,
`E_{µ₀}(1 − ξ₊)₊⁴(1 − ξ₋)₊⁴ ≥ c_Schur` (B.15), where `dµ₀ = (w₀/Ew₀) dγₙ`.

**Formalization Note.**
* `d = m + 1`; the splitting `span{v} ⊕ v^⊥` is given by an orthogonal `Q` whose column `0` is `v`
  (then `v` is a unit vector). The left side does not depend on the orthonormal basis of `v^⊥`, so
  the statement for every such `Q` is the page's statement.
* `∑ᵢ Aᵢ² ⪯ I_d` is `I − ∑ᵢ Aᵢ²` positive semidefinite, before the factor `¼`.
* `E_{µ₀} F` is written as `(∫ F w₀ dγₙ) / (∫ w₀ dγₙ)`; `(t)₊ = max t 0`. `ξ±` are read only where
  `w₀ ≠ 0`, i.e. on `Ω₀`. -/
theorem theorem_B_2 {n m : ℕ} (A : Fin n → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hAA : (1 - ∑ i, A i ^ 2).PosSemidef)
    (v : E (m + 1)) (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ) (hQv : ∀ j, Q j 0 = v j) :
    cSchur ≤
      (∫ g, max (1 - xiPlus A Q g) 0 ^ 4 * max (1 - xiMinus A Q g) 0 ^ 4 * w0 A Q g ∂(gam n)) /
        ∫ g, w0 A Q g ∂(gam n) := by sorry

end MatrixSpencer.Supplement
