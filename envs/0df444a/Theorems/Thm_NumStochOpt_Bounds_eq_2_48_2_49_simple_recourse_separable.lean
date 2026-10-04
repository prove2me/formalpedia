-- Prove2me | Theorems.Thm_NumStochOpt_Bounds_eq_2_48_2_49_simple_recourse_separable
-- name    : NumStochOpt.Bounds.eq_2_48_2_49_simple_recourse_separable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T19:16:09.36942+00:00
-- url     : https://prove2.me/theorems/2c67119f-df1c-42b4-bcc7-df79543a4d41
-- title:
--   Eqs. (2.46)–(2.49) — the simple-recourse cost separates into one-row costs
-- statement:
--   Let $W=[I,-I]$ (simple recourse), $q=[q^+,q^-]$ with $q_j^++q_j^-\ge0$ for every $j$, $T$ a deterministic $m_2\times n_1$ matrix, $h\in\mathbb R^{m_2}$ and $x\in\mathbb R^{n_1}$; write $\chi=Tx$. Then the optimal value $Q(\chi,h)$ of
--   $$
--   \min\ (q^+)^Ty^++(q^-)^Ty^-\quad\text{s.t.}\quad y^+-y^-=h-\chi,\ y^+\ge0,\ y^-\ge0 \tag{2.46}
--   $$
--   is finite and
--   $$
--   Q(\chi,h)=\sum_{j=1}^{m_2}Q_j(\chi_j,h_j), \tag{2.48}
--   $$
--   where, by (2.49), $Q_j(\chi_j,h_j)=q_j^+(h_j-\chi_j)$ if $h_j\ge\chi_j$ and $q_j^-(\chi_j-h_j)$ if $h_j<\chi_j$.
--
--   This separability is what reduces every bound for simple recourse to one-dimensional integrals.
--
--   **Formalization Note** The left-hand side is the general extended-real recourse cost with $W=[I,-I]$ and cost vector $[q^+,q^-]$; the right-hand side is the closed form of p. 53. The book's condition $q^++q^-\ge0$ (p. 53, assumed "from now on") is a hypothesis.
-- source:
--   P. Kall, A. Ruszczyński, K. Frauendorfer, "Approximation Techniques in Stochastic Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 2, pp. 52-53, Eqs. (2.46)-(2.49)

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_RecourseCost
import Definitions.Def_NumStochOpt_Bounds_SimpleRecourse

open Matrix

namespace NumStochOpt.Bounds

/-- Eqs. (2.46)–(2.49), pp. 52–53: for simple recourse `W = [I, −I]`, `q = [q⁺, q⁻]` with
`q⁺_j + q⁻_j ≥ 0` for every `j`, the optimal value of (2.46) at `χ = T x` is finite and splits
as `Q(χ, h) = Σ_j Q_j(χ_j, h_j)` with `Q_j` the closed form (2.49). -/
theorem eq_2_48_2_49_simple_recourse_separable {ι ν : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ν] (qp qm : ι → ℝ) (hq : ∀ j, 0 ≤ qp j + qm j) (T : Matrix ι ν ℝ) (h : ι → ℝ)
    (x : ν → ℝ) :
    recourseCost (simpleRecourseMatrix ι) (Sum.elim qp qm) h T x =
      ((∑ j, simpleRecourseCost (qp j) (qm j) ((T *ᵥ x) j) (h j) : ℝ) : EReal) := by sorry

end NumStochOpt.Bounds
