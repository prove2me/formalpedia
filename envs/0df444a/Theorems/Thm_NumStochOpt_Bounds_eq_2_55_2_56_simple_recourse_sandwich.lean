-- Prove2me | Theorems.Thm_NumStochOpt_Bounds_eq_2_55_2_56_simple_recourse_sandwich
-- name    : NumStochOpt.Bounds.eq_2_55_2_56_simple_recourse_sandwich
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T19:24:14.092838+00:00
-- url     : https://prove2.me/theorems/31bcde07-8363-4f59-8ba0-d4f7861dd5af
-- title:
--   Eqs. (2.55)–(2.56) — lower and upper bounds for simple recourse from the one-block problem
-- statement:
--   Consider the simple-recourse problem with deterministic $A$, $b$, $c$, $T$, costs $q^+,q^-$ with $q_j^++q_j^-\ge0$, and a random right-hand side $h(\omega)$ whose coordinates $h_j$ are measurable with values in $[a_j,b_j]$ almost surely. Let $h^1=Eh(\omega)$ and let $(\tilde x,\tilde y^+,\tilde y^-)$ solve the one-block linear program
--   $$
--   \min\ c^Tx+(q^+)^Ty^++(q^-)^Ty^-\quad\text{s.t.}\quad Ax=b,\ Tx+Iy^+-Iy^-=h^1,\ x\ge0,\ y^+\ge0,\ y^-\ge0, \tag{2.53}
--   $$
--   and put $\tilde\chi=T\tilde x$. Then
--   $$
--   Q_j(\tilde\chi_j,h_j^1)\le EQ_j(\tilde\chi_j,h_j(\omega)),\qquad j=1,\dots,m_2, \tag{2.55}
--   $$
--   and
--   $$
--   c^T\tilde x+\sum_{j=1}^{m_2}Q_j(\tilde\chi_j,h_j^1)\;\le\;\min_{Ax=b,\,x\ge0}\big[c^Tx+EQ(Tx,h(\omega))\big]\;\le\;c^T\tilde x+\sum_{j=1}^{m_2}EQ_j(\tilde\chi_j,h_j(\omega)). \tag{2.56}
--   $$
--   Here $Q(\chi,h)$ is the optimal value of the simple-recourse problem (2.46) and $Q_j$ its one-row pieces.
--
--   The two sides are computable (an LP and one-dimensional integrals), and they bracket the optimal value of the stochastic problem; they are the starting point of the partition refinement of §2.2.5.
--
--   **Formalization Note** The middle term is an infimum over the first-stage feasible set $\{x: Ax=b,\ x\ge0\}$ (a real `sInf`), which is nonempty since it contains $\tilde x$; the statement does not claim the infimum is attained. The optimal solution of (2.53) is a hypothesis: feasibility plus optimality against every feasible triple. $EQ(Tx,h)$ is the expected extended-real recourse cost with $W=[I,-I]$ and cost $[q^+,q^-]$.
-- source:
--   P. Kall, A. Ruszczyński, K. Frauendorfer, "Approximation Techniques in Stochastic Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 2, p. 55, Eqs. (2.53)-(2.56)

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_RecourseCost
import Definitions.Def_NumStochOpt_Bounds_SimpleRecourse

open MeasureTheory Matrix

namespace NumStochOpt.Bounds

/-- Eqs. (2.55)–(2.56), p. 55: simple recourse `W = [I, −I]`, deterministic `q = [q⁺, q⁻]` with
`q⁺_j + q⁻_j ≥ 0` and `T`, random right-hand side `h(ω)` in the box `×_j [a_j, b_j]`. If
`(x̃, ỹ⁺, ỹ⁻)` solves the one-block problem (2.53) with `h¹ = E h(ω)` and `χ̃ = T x̃`, then
`Q_j(χ̃_j, h¹_j) ≤ E Q_j(χ̃_j, h_j(ω))` for every `j`, and
`cᵀx̃ + Σ_j Q_j(χ̃_j, h¹_j) ≤ min_{Ax=b, x≥0} [cᵀx + E Q(Tx, h(ω))] ≤ cᵀx̃ + Σ_j E Q_j(χ̃_j, h_j(ω))`. -/
theorem eq_2_55_2_56_simple_recourse_sandwich {Ω ι ρ ν : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Fintype ρ] [Fintype ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Matrix ρ ν ℝ) (bvec : ρ → ℝ) (c : ν → ℝ) (T : Matrix ι ν ℝ)
    (qp qm : ι → ℝ) (hq : ∀ j, 0 ≤ qp j + qm j)
    (h : Ω → ι → ℝ) (hmeas : ∀ j, Measurable fun ω => h ω j)
    (a b : ι → ℝ) (hab : ∀ j, a j ≤ b j) (hsupp : ∀ᵐ ω ∂P, ∀ j, h ω j ∈ Set.Icc (a j) (b j))
    (xt : ν → ℝ) (ypt ymt : ι → ℝ)
    (hfeas : A *ᵥ xt = bvec ∧ T *ᵥ xt + ypt - ymt = (fun j => ∫ ω, h ω j ∂P) ∧
      0 ≤ xt ∧ 0 ≤ ypt ∧ 0 ≤ ymt)
    (hopt : ∀ (x : ν → ℝ) (yp ym : ι → ℝ), A *ᵥ x = bvec →
      T *ᵥ x + yp - ym = (fun j => ∫ ω, h ω j ∂P) → 0 ≤ x → 0 ≤ yp → 0 ≤ ym →
      c ⬝ᵥ xt + qp ⬝ᵥ ypt + qm ⬝ᵥ ymt ≤ c ⬝ᵥ x + qp ⬝ᵥ yp + qm ⬝ᵥ ym) :
    (∀ j, simpleRecourseCost (qp j) (qm j) ((T *ᵥ xt) j) (∫ ω, h ω j ∂P) ≤
        ∫ ω, simpleRecourseCost (qp j) (qm j) ((T *ᵥ xt) j) (h ω j) ∂P) ∧
      c ⬝ᵥ xt + ∑ j, simpleRecourseCost (qp j) (qm j) ((T *ᵥ xt) j) (∫ ω, h ω j ∂P) ≤
        sInf ((fun x => c ⬝ᵥ x + expectedRecourse P (simpleRecourseMatrix ι)
            (fun _ => Sum.elim qp qm) h (fun _ => T) x) '' {x | A *ᵥ x = bvec ∧ 0 ≤ x}) ∧
      sInf ((fun x => c ⬝ᵥ x + expectedRecourse P (simpleRecourseMatrix ι)
            (fun _ => Sum.elim qp qm) h (fun _ => T) x) '' {x | A *ᵥ x = bvec ∧ 0 ≤ x}) ≤
        c ⬝ᵥ xt + ∑ j, ∫ ω, simpleRecourseCost (qp j) (qm j) ((T *ᵥ xt) j) (h ω j) ∂P := by sorry

end NumStochOpt.Bounds
