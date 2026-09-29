-- Prove2me | Theorems.Thm_LassoDantzig_Oracle_cone_step
-- name    : LassoDantzig.Oracle.cone_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:09:49.113612+00:00
-- url     : https://prove2.me/theorems/83d632fd-8574-4d31-816f-4d6fc440d17b
-- title:
--   Proof of Theorem 6.1 — in case (B.24) the Lasso error lies in the cone with constant $(3+4/\varepsilon)f_{\max}/f_{\min}$
-- statement:
--   Let $n\ge1$, $M\ge2$, $X\in\mathbb R^{n\times M}$ with nonzero column norms, $f,y\in\mathbb R^n$, $r>0$, $\varepsilon>0$, and suppose $w=y-f$ lies in the noise event $\mathcal A$ ($2|n^{-1}\sum_iX_{ij}w_i|\le r\|f_j\|_n$ for all $j$). Let $\hat\beta$ be any Lasso solution (2.1) for $y$ with tuning constant $r$, let $\beta\in\mathbb R^M$, $J_0=J(\beta)$, and let $\delta=D^{1/2}(\hat\beta-\beta)$, i.e. $\delta_j=\|f_j\|_n(\hat\beta_j-\beta_j)$. Assume case (B.24):
--   $$\varepsilon\|X\beta-f\|_n^2<4r|\delta_{J_0}|_1 .$$
--   Then
--   $$|\delta|_1\le4(1+1/\varepsilon)|\delta_{J_0}|_1,\qquad |\delta_{J_0^c}|_1\le(3+4/\varepsilon)|\delta_{J_0}|_1,$$
--   and the unweighted difference $\delta'=\hat\beta-\beta$ satisfies
--   $$|\delta'_{J_0^c}|_1\le(3+4/\varepsilon)\frac{f_{\max}}{f_{\min}}|\delta'_{J_0}|_1 .$$
--
--   This is the step that places the Lasso error in the cone of Assumption RE$(s,(3+4/\varepsilon)f_{\max}/f_{\min})$, explaining the cone constant in Theorem 6.1.
--
--   **Formalization Note** The page states these inequalities "on the event $\mathcal A\cap\mathcal A_1$"; here the event is written deterministically for a fixed noise vector, and the statement holds for any $r>0$ (the proof does not use the value of $r$).
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 26, Appendix B, proof of Theorem 6.1, first display and the sentence after it (case (B.24), p. 25)

import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

/-- **Cone step in the proof of Theorem 6.1** (p. 26, first display). On the event `𝒜`, for
every Lasso solution `β̂` with tuning constant `r > 0` and every `β` in case (B.24),
`ε‖f_β − f‖_n² < 4r|δ_{J₀}|_1`, where `δ = D^{1/2}(β̂ − β)` (so `|δ_j| = ‖f_j‖_n |β̂_j − β_j|`) and
`J₀ = J(β)`: `|δ|_1 ≤ 4(1 + 1/ε)|δ_{J₀}|_1`, hence `|δ_{J₀ᶜ}|_1 ≤ (3 + 4/ε)|δ_{J₀}|_1`, and the
unweighted `δ' = β̂ − β` satisfies `|δ'_{J₀ᶜ}|_1 ≤ (3 + 4/ε)(f_max/f_min)|δ'_{J₀}|_1`. -/
theorem cone_step {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ)
    (hcol : ∀ j, colNorm X j ≠ 0) (f y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hA : NoiseBound X (fun i => y i - f i) r) (ε : ℝ) (hε : 0 < ε)
    (βhat : Fin M → ℝ) (hL : IsLasso X y r βhat) (β : Fin M → ℝ)
    (hB24 : ε * empSq (fun i => X.mulVec β i - f i) <
      4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j|) :
    ∑ j, colNorm X j * |βhat j - β j| ≤
        4 * (1 + 1 / ε) * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ∧
      ∑ j ∈ (supp β)ᶜ, colNorm X j * |βhat j - β j| ≤
        (3 + 4 / ε) * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ∧
      ConeCond ((3 + 4 / ε) * fmax X / fmin X) (supp β) (βhat - β) := by sorry

end LassoDantzig.Oracle
