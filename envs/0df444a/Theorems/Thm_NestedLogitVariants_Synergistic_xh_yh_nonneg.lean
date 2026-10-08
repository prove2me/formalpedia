-- Prove2me | Theorems.Thm_NestedLogitVariants_Synergistic_xh_yh_nonneg
-- name    : NestedLogitVariants.Synergistic.xh_yh_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:26:12.04374+00:00
-- url     : https://prove2.me/theorems/0c91eee4-778c-4250-926d-d16906e4e9be
-- title:
--   Appendix A.1, p. 41 — an optimal solution of (4) over the nested-by-revenue assortments has ŷ ≥ 0 and x̂ ≥ 0
-- statement:
--   Let $(\hat x, \hat y)$ be an optimal solution of the linear program (4) in which the candidate collections are the nested-by-revenue assortments $\{N_{ij} : j \in N_+\}$, $N_+ = \{0, 1, \dots, n\}$, $N_{i0} = \emptyset$, for an instance with fully-captured nests. Then
--
--   $$\hat y_i \ge 0 \quad \text{for all } i \in M, \qquad \hat x \ge 0.$$
--
--   These sign conditions are used throughout the proof of Theorem 7 to enlarge the coefficients of $\hat y_i$ and $\hat x$.
--
--   **Formalization Note** The standing assumptions are those of the model (see the Model definition) and of §4: every nest is fully captured, $v_{i0} = 0$, and $\gamma_i > 1$ for some nest $i$ (p. 16). An optimal solution of (4) is a feasible pair whose $x$ is no larger than that of any feasible pair. The page argues $\hat x \ge 0$ from the first constraint of (4), which needs $v_0 > 0$; no hypothesis on $v_0$ is added, because when $v_0 = 0$ optimality forces $\hat x = \max_{i, j} R_i(N_{ij}) \ge 0$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 41, Appendix A.1 (first paragraph)

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Model

namespace NestedLogitVariants.Synergistic

/-- Appendix A.1, p. 41: an optimal solution `(x̂, ŷ)` of (4) over the nested-by-revenue assortments
`{N_{ij} : j ∈ N_+}` has `ŷ_i ≥ 0` for every nest and `x̂ ≥ 0`. -/
theorem xh_yh_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (fun _ => {S | ∃ j ≤ n, S = nbr n j}) xh yh) :
    (∀ i, 0 ≤ yh i) ∧ 0 ≤ xh := by sorry

end NestedLogitVariants.Synergistic
