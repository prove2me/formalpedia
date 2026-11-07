-- Prove2me | Theorems.Thm_IterRoundDet_lemma_3_9
-- name    : IterRoundDet.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:12.733468+00:00
-- url     : https://prove2.me/theorems/655f15b1-2acf-4367-a16e-00739a60a790
-- title:
--   Lemma 3.9 — second derivatives of $f-g_1$ and $f-g_2$ along a balanced direction, (28)
-- statement:
--   Let $(a,x)\in\mathcal R$ be a proportional pair, $C$ the covariance of $\mu_a$, $v$ a balanced direction, and $w$ as in (25). For small $|t|$ the point $(a+tv,x+tw)$ stays in $\mathcal R$ and proportional, and
--
--   $$\frac{d^2}{dt^2}(f-g_1)(a+tv,x+tw)\Big|_{t=0}=\sum_{i\in A}\frac{v_i^2}{a_i}+12\sum_{i\in A}\frac{v_i^2}{1-a_i}-v^\top C^\dagger v,$$
--
--   $$\frac{d^2}{dt^2}(f-g_2)(a+tv,x+tw)\Big|_{t=0}=3\sum_{i\in A}\frac{v_i^2}{a_i(1-a_i)}-v^\top C^\dagger v.$$
--
--   **Formalization Note** Each function is $C^2$ at $t=0$, stated together with each formula; this guards the junk value of a Lean second derivative.
--
--   Differences from the source:
--   - encoding: a homogeneous multiaffine polynomial p of degree d → its coefficient function c with c S ≠ 0 → |S| = d; reason: footnote 2 is this form; the two are in bijection
--   - encoding: all coefficients have the same sign → non-negative coefficients inside IsStablePoly; reason: footnote 2 and §3.1 normalize to this; for a negative p the printed logarithms have no meaning
--   - encoding: d²/dt² at t = 0 → deriv (deriv φ) 0, plus ContDiffAt ℝ 2 φ 0; reason: ContDiffAt guards the junk value of deriv
--   - generalization: the two formulas (28) → also: for all small |t| the point (a + tv, x + tw) is in R and proportional; reason: the sentence after (25) on the same page asserts it; the printed formulas are conjuncts, so the item specializes to the lemma
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.9, (28), and the sentence after (25), p.17

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Polytopes
import Definitions.Def_IterRoundDet_Relaxation
import Definitions.Def_IterRoundDet_Regularizer
import Definitions.Def_IterRoundDet_Covariance

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.9, (28), p.17. For a proportional pair, a balanced `v`, and `w` as in (25),
`d²/dt² (f − g₁)(a + tv, x + tw)|_{t=0} = ∑_{i∈A} v_i²/a_i + 12 ∑_{i∈A} v_i²/(1 − a_i) − v⊤C†v` and
`d²/dt² (f − g₂)(a + tv, x + tw)|_{t=0} = 3 ∑_{i∈A} v_i²/(a_i(1 − a_i)) − v⊤C†v`. It also includes the sentence before the
lemma, p.17: the line `(a, x) + t(v, w)` keeps the pair proportional, for small `|t|`.

**Formalization Note.** `ContDiffAt ℝ 2` guards the junk value of `deriv`. The line stays in `R` for small `|t|`, which is
where `f` is meaningful. -/
theorem lemma_3_9 {n d : ℕ} {c : Finset (Fin n) → ℝ} (hc : IsStablePoly d c)
    {M : Matroid (Fin n)} (hM : M.E = Set.univ) {a x : Fin n → ℝ} (hax : Feasible c M a x)
    {π : Finpartition (fractional x)} (hπ : IsFacePartition M x π) (hprop : IsProportional a x π)
    {μ : Finset (Fin n) → ℝ} (hμ : IsMaxEnt c a μ) {v : Fin n → ℝ} (hv : IsBalanced c a π v) :
    (∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, |t| < t₀ →
      Feasible c M (a + t • v) (x + t • extendDir a x v) ∧
      IsProportional (a + t • v) (x + t • extendDir a x v) π) ∧
    ContDiffAt ℝ 2 (fun t : ℝ => fMinusG1 c d (a + t • v) (x + t • extendDir a x v)) 0 ∧
    deriv (deriv fun t : ℝ => fMinusG1 c d (a + t • v) (x + t • extendDir a x v)) 0 =
      ∑ i ∈ fractional x, v i ^ 2 / a i + 12 * ∑ i ∈ fractional x, v i ^ 2 / (1 - a i) -
        pinvForm (covMat μ a) v ∧
    ContDiffAt ℝ 2 (fun t : ℝ => fMinusG2 c (a + t • v) (x + t • extendDir a x v)) 0 ∧
    deriv (deriv fun t : ℝ => fMinusG2 c (a + t • v) (x + t • extendDir a x v)) 0 =
      3 * ∑ i ∈ fractional x, v i ^ 2 / (a i * (1 - a i)) - pinvForm (covMat μ a) v := by sorry

end IterRoundDet
