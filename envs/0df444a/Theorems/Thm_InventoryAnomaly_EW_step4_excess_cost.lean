-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_step4_excess_cost
-- name    : InventoryAnomaly.EW.step4_excess_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:57.626619+00:00
-- url     : https://prove2.me/theorems/25bdbacd-3db6-4ab4-ac49-39d8e3fa72b2
-- title:
--   Proof sketch of Theorem 1, Step 4, p. 23 — the excess cost equals Σ(1{a≤0} − 1{b≤0})b/|Ω| and is at most Σ|a − b|/|Ω|
-- statement:
--   Fix an instance whose costs $c^{(0)}_{ij},c^{(1)}_{ij}$ are nonnegative, any rank-$r$ selector and any estimator $\hat\theta$, and an observation $X_\Omega$. Define
--   $$a_{ij}=-c^{(1)}_{ij}+\big(c^{(0)}_{ij}+c^{(1)}_{ij}\big)\hat f_{ij},\qquad b_{ij}=-c^{(1)}_{ij}+\big(c^{(0)}_{ij}+c^{(1)}_{ij}\big)f^*_{ij}.$$
--   Then
--   $$\mathrm{cost}^{\pi^{EW}}(X_\Omega)-\mathrm{cost}^{\pi^*}(X_\Omega)=\frac1{|\Omega|}\sum_{(i,j)\in\Omega}\big(\mathbf 1\{a_{ij}\le0\}-\mathbf 1\{b_{ij}\le0\}\big)b_{ij}\le\frac1{|\Omega|}\sum_{(i,j)\in\Omega}|a_{ij}-b_{ij}| .$$
--
--   This reduces the excess cost of the EW algorithm to the estimation error $|\hat f_{ij}-f^*_{ij}|$, weighted by $c^{(0)}_{ij}+c^{(1)}_{ij}$.
--
--   **Formalization Note.** The costs are those of the closed form (5) with deterministic decisions. Nonnegativity of the costs (assumed on p. 11) is needed: it makes the threshold rule "$f\le c^{(1)}/(c^{(0)}+c^{(1)})$" equivalent to $a\le0$; when $c^{(0)}_{ij}+c^{(1)}_{ij}=0$ both costs vanish and the entry contributes nothing.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 23, proof sketch of Theorem 1, Step 4

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem step4_excess_cost {d : ℕ} (I : Instance d)
    (hc : ∀ i j, 0 ≤ I.c0 i j ∧ 0 ≤ I.c1 i j)
    (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
    (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))) (x : I.Obs) :
    let a := fun i j => -I.c1 i j + (I.c0 i j + I.c1 i j) * I.fhat svdr θhat x i j
    let b := fun i j => -I.c1 i j + (I.c0 i j + I.c1 i j) * I.fstar x i j
    I.costEW svdr θhat x - I.costStar x =
        (1 / ((I.omega x).card : ℝ)) * ∑ ij ∈ I.omega x,
          ((if a ij.1 ij.2 ≤ 0 then 1 else 0) - (if b ij.1 ij.2 ≤ 0 then 1 else 0)) * b ij.1 ij.2 ∧
      I.costEW svdr θhat x - I.costStar x ≤
        (1 / ((I.omega x).card : ℝ)) * ∑ ij ∈ I.omega x, |a ij.1 ij.2 - b ij.1 ij.2| := by sorry

end InventoryAnomaly.EW
