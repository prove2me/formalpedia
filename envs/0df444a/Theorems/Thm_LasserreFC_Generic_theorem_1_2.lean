-- Prove2me | Theorems.Thm_LasserreFC_Generic_theorem_1_2
-- name    : LasserreFC.Generic.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:32.196412+00:00
-- url     : https://prove2.me/theorems/79b2d1e6-1eeb-4d0f-9f65-8fd6f404a525
-- title:
--   Theorem 1.2, p. 3 — off a proper Zariski-closed set of input data, CQC, strict complementarity and SOSC hold at every local minimizer
-- statement:
--   Let $d_0,d_1,\dots,d_{m_1},d'_1,\dots,d'_{m_2}$ be positive integers. Then there are finitely many real polynomials $\phi_1,\dots,\phi_L$ in the coefficients of $f\in\mathbb R[x]_{d_0}$, $h_i\in\mathbb R[x]_{d_i}$ ($i\in[m_1]$), $g_j\in\mathbb R[x]_{d'_j}$ ($j\in[m_2]$) such that
--   1. some admissible input $(f,h,g)$ makes every $\phi_l$ nonzero, and
--   2. whenever $\phi_1,\dots,\phi_L$ do not vanish at the input $(f,h,g)$, the constraint qualification, strict complementarity and second order sufficiency conditions hold at every local minimizer $u$ of
--   $$\min\ f(x)\quad\text{s.t.}\quad h_i(x)=0\ (i\in[m_1]),\quad g_j(x)\ge0\ (j\in[m_2]).$$
--
--   So these classical optimality conditions hold on a nonempty Zariski open subset of the space of input data, which is dense and whose complement has Lebesgue measure zero. Combined with Theorem 1.1 of the same paper, this explains why Lasserre's hierarchy generically has finite convergence under archimedeanness.
--
--   **Formalization Note** Item 1 is not printed in the theorem: as printed, $\phi_1=0$ would satisfy the statement. It is the paper's own reading ("they hold in a Zariski open set", p. 3; Appendix A shows the relevant polynomials do not vanish identically), and it is asserted at an admissible input because coefficient variables of monomials above the degree bound vanish on every admissible input. No restriction $m_1\le n$ is imposed, as on the page: Condition 4.3 assumes it, but for $m_1>n$ a single resultant of $h_1,\dots,h_{n+1}$ already makes $K$ empty off its zero set.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 3, Theorem 1.2 (proof p. 16; Condition 4.3, p. 14)

import Mathlib
import Definitions.Def_LasserreFC_Generic_Setting

namespace LasserreFC.Generic

open MvPolynomial

/-- Theorem 1.2, p. 3. Let `d₀, d₁, …, d_{m₁}, d'₁, …, d'_{m₂}` be positive integers.
There are finitely many real polynomials `ϕ₁, …, ϕ_L` in the coefficients of
`f ∈ ℝ[x]_{d₀}`, `hᵢ ∈ ℝ[x]_{dᵢ}`, `gⱼ ∈ ℝ[x]_{d'ⱼ}`, with some admissible input at which none of
them vanishes, such that whenever no `ϕₗ` vanishes at the input polynomials, the constraint
qualification, strict complementarity and second order sufficiency conditions hold at every local
minimizer of (1.1). -/
theorem theorem_1_2 {n m1 m2 : ℕ} (d0 : ℕ) (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ)
    (hd0 : 0 < d0) (hd : ∀ i, 0 < d i) (hd' : ∀ j, 0 < d' j) :
    ∃ (L : ℕ) (ϕ : Fin L → MvPolynomial (CoefIdx n m1 m2) ℝ),
      (∃ P₀ : POP n m1 m2, P₀.Admissible d0 d d' ∧
        ∀ l, MvPolynomial.eval (coeffs P₀) (ϕ l) ≠ 0) ∧
      ∀ P : POP n m1 m2, P.Admissible d0 d d' →
        (∀ l, MvPolynomial.eval (coeffs P) (ϕ l) ≠ 0) →
        ∀ u ∈ P.K, IsLocalMinOn (fun x => eval x P.f) P.K u → OptCond P u := by sorry

end LasserreFC.Generic
