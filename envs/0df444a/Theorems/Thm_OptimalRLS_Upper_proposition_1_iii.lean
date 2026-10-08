-- Prove2me | Theorems.Thm_OptimalRLS_Upper_proposition_1_iii
-- name    : OptimalRLS.Upper.proposition_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:25:28.318932+00:00
-- url     : https://prove2.me/theorems/5ab2fef0-d030-489c-b176-29fd46e42ab9
-- title:
--   Proposition 1 iii), (24), p. 12 — E[f] − E[f_H] = ‖√T (f − f_H)‖²_H
-- statement:
--   Assume Hypotheses 1 and 2, and let $f_{\mathcal H}$ be a minimizer of the expected risk $\mathcal E$ over $\mathcal H$. Then for every $f\in\mathcal H$,
--   $$\mathcal E[f]-\mathcal E[f_{\mathcal H}]=\big\|\sqrt T\,(f-f_{\mathcal H})\big\|_{\mathcal H}^2=\int_X\|f(x)-f_{\mathcal H}(x)\|_Y^2\,d\rho_X(x).$$
--
--   The excess risk is therefore a squared norm in $\mathcal H$ weighted by $T$; every later bound on $\mathcal E[f_{\mathbf z}^\lambda]-\mathcal E[f_{\mathcal H}]$ starts from this identity.
--
--   **Formalization Note** $\|\sqrt T h\|_{\mathcal H}^2=\langle Th,h\rangle_{\mathcal H}$ is written as `covForm ρ.fst h h` $=\int_X\langle h(x),h(x)\rangle_Y\,d\rho_X$, by (29). The minimizer property (8) is part of `Hyp2`; any minimizer works here, not only the minimal-norm one.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proposition 1 iii), (24), p. 12; (29), p. 13

import Mathlib
import Definitions.Def_OptimalRLS_Upper_Setting

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace OptimalRLS.Upper

/-- **Proposition 1 iii), (24)** (p. 12). Under Hypotheses 1 and 2, for every `f ∈ H`,
`E[f] − E[f_H] = ‖√T (f − f_H)‖²_H`, where `‖√T h‖²_H = ⟨T h, h⟩_H = ∫_X ‖h(x)‖²_Y dρ_X(x)`
(by (29)) is `covForm ρ.fst h h`. -/
theorem proposition_1_iii
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]
    {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) (h1 : Hyp1 X H κ v)
    (M Sig : ℝ) (ρ : Measure (X × Y)) [IsProbabilityMeasure ρ] (fH : H)
    (h2 : Hyp2 M Sig ρ fH) (f : H) :
    risk ρ f - risk ρ fH = covForm ρ.fst (f - fH) (f - fH) := by sorry

end OptimalRLS.Upper
