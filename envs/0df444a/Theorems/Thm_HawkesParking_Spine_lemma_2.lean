-- Prove2me | Theorems.Thm_HawkesParking_Spine_lemma_2
-- name    : HawkesParking.Spine.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:20.891214+00:00
-- url     : https://prove2.me/theorems/675d30bd-81e7-44b6-b1aa-00a3cec43a4c
-- title:
--   Lemma 2, p. 10 — given $N=k+1$, the compensator points are uniform on $\mathcal P_k$
-- statement:
--   Let $g$ be an excitation kernel satisfying the standing assumptions, with $\rho=\int_0^\infty g\in(0,1)$, and let $k\in\mathbb N$. Given that the cluster has $N=k+1$ events (including the initial event at time $0$), the compensator points $(\Lambda_1,\dots,\Lambda_k)$ have the conditional joint density
--   $$f(\Lambda_1,\dots,\Lambda_k\mid N=k+1)=\Big(\frac1\rho\Big)^k\frac{(k+1)!}{(k+1)^k}$$
--   on the polytope $\mathcal P_k=\{x\in\mathbb R^k_+: x_i<i\rho\ \forall i,\ x_1<\dots<x_k\}$. Hence
--   $$\Lambda\mid N=k+1\ \sim\ \mathrm{Uni}(\mathcal P_k).$$
--
--   This is the conditional random time change theorem of the paper: given its size, a Hawkes cluster's compensator points are uniform on a polytope that depends on $g$ only through $\rho$.
--
--   **Formalization Note.** Both parts are stated as equalities of measures on $\mathbb R^k$: the conditional law equals the constant density times Lebesgue measure on $\mathcal P_k$, and it equals the normalized Lebesgue measure on $\mathcal P_k$. The conditional law is the image of the likelihood-defined cluster law under the compensator map divided by its total mass (see the Model item).
-- source:
--   Daw, Conditional Uniformity and Hawkes Processes, arXiv:2202.05335v2, p. 10, Lemma 2, eq. (7)

import Mathlib
import Definitions.Def_HawkesParking_Spine_Model

namespace HawkesParking.Spine
open MeasureTheory
theorem lemma_2 (g : ℝ → ℝ) (hg : IsKernel g) (k : ℕ) :
    condCompensatorLaw g k =
        ENNReal.ofReal ((1 / rho g) ^ k * ((k + 1).factorial : ℝ) / ((k : ℝ) + 1) ^ k) •
          volume.restrict (polytope k (rho g)) ∧
      condCompensatorLaw g k = unif (polytope k (rho g)) := by sorry
end HawkesParking.Spine
