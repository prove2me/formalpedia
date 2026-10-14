-- Prove2me | Theorems.Thm_MultiStoreAssort_Approx_tightness_instance
-- name    : MultiStoreAssort.Approx.tightness_instance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:53.115175+00:00
-- url     : https://prove2.me/theorems/2c25d46a-26de-4684-8d94-9c89990ad7e1
-- title:
--   Proof of Proposition 7, PDF p. 47 — the tightness instance: S̃ = {1}, ({1},{1}) earns 1, ({1},{2}) earns nearly 2
-- statement:
--   Fix $0<\epsilon<1$ and consider the instance with two stores and two products in which the arrival fractions are $\lambda_1=1$, $\lambda_2=0$, the revenues are $r_1=1+\frac1\epsilon$ and $r_2=1$, the attraction values are $v_{i1}=\epsilon$ and $v_{i2}=\frac1\epsilon$ in both stores $i=1,2$, and every utility discount $c^k_{ij}$ is $0$. Then:
--
--   1. In both stores the smallest revenue-ordered optimal single-store assortment is $\tilde S=\{1\}$ (both $\{1\}$ and $\{1,2\}$ earn $1$; $\{2\}$ earns $\frac1{1+\epsilon}$).
--   2. The heuristic profile $(\{1\},\{1\})$ earns exactly $1$ under (SQR-heter).
--   3. The profile $(\{1\},\{2\})$ earns
--   $$
--   1+\frac{1}{(1+\epsilon)(1+\epsilon+\epsilon^2)},
--   $$
--   which tends to $2$ as $\epsilon\to0$.
--
--   This is the instance showing that the factor $\frac12$ of Proposition 7 cannot be improved.
--
--   **Formalization Note.** The paper says only that the two revenues are "close to 1" and "close to 2" when $\epsilon\to0$; the exact values above are a direct computation from (10). The paper sets $c^1_{12}=c^2_{12}=0$ and leaves the other cross-store discounts unspecified; they are set to $0$ here, which does not affect the revenues because $\lambda_2=0$ and the discounts $c^k_{ii}$ are $0$ by assumption.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 47 (Online Supplement p. 15), Appendix D.2, proof of Proposition 7, tightness instance

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MultiStoreAssort_Approx_Model

namespace MultiStoreAssort.Approx

/-- The tightness instance of the proof of Proposition 7 (Online Supplement p. 15): two stores, two
products, `λ = (1, 0)`, revenues `(1 + 1/ε, 1)`, attraction values `(ε, 1/ε)` in both stores and all
utility discounts `0`. Then `S̃ = {1}` in both stores, the profile `({1}, {1})` earns exactly `1`, and
the profile `({1}, {2})` earns `1 + 1/((1 + ε)(1 + ε + ε²))`, which tends to `2` as `ε → 0`. -/
theorem tightness_instance (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    let lam : Fin 2 → ℝ := ![1, 0]
    let r : Fin 2 → ℝ := ![1 + 1 / ε, 1]
    let v : Fin 2 → Fin 2 → ℝ := fun _ => ![ε, 1 / ε]
    let c : Fin 2 → Fin 2 → Fin 2 → ℝ := fun _ _ _ => 0
    (∀ (i : Fin 2) (S : Finset (Fin 2)), MultiStoreAssort.SMR.IsStilde r (v i) S ↔ S = {0}) ∧
      revQh lam r v c ![{0}, {0}] = 1 ∧
      revQh lam r v c ![{0}, {1}] = 1 + 1 / ((1 + ε) * (1 + ε + ε ^ 2)) := by sorry

end MultiStoreAssort.Approx
