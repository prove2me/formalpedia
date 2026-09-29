-- Prove2me | Theorems.Thm_LearnStability_ConvexSCO_erm_replace_one_stability
-- name    : LearnStability.ConvexSCO.erm_replace_one_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:15:42.850871+00:00
-- url     : https://prove2.me/theorems/0b2be463-3dcc-453f-992d-cdd959b07b51
-- title:
--   Eq. (6): the strongly convex empirical minimizer is replace-one stable, $|f(\hat h_S,z)-f(\hat h_S^{(i)},z)|\le 4L^2/(\lambda m)$
-- statement:
--   Consider a stochastic convex optimization problem on $\mathcal H$ whose objective $f(h;z)$ is, for every $z$, $\lambda$-strongly convex ($\lambda>0$) and $L$-Lipschitz in $h\in\mathcal H$. Let $S=(z_1,\dots,z_m)$ with $m\ge1$, fix an index $i$ and a replacement instance $z'_i$, and let $S^{(i)}$ be $S$ with $z_i$ replaced by $z'_i$. Let $\hat h_S\in\mathcal H$ minimize $F_S$ over $\mathcal H$ and $\hat h_S^{(i)}\in\mathcal H$ minimize $F_{S^{(i)}}$ over $\mathcal H$. Then
--   $$\forall z\in Z,\qquad \big|f(\hat h_S,z)-f(\hat h_S^{(i)},z)\big|\ \le\ \frac{4L^2}{\lambda m}.$$
--
--   This is a deterministic statement: it holds for every sample and every replacement. It says that empirical minimization of a strongly convex objective is uniform-RO stable with rate $4L^2/(\lambda m)$.
--
--   **Formalization Note** The paper's stochastic convex optimization standing assumptions (closed, bounded $\mathcal H$, $|f|\le C$, measurability) are carried in the hypothesis bundle although this step does not use them.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2645, Eq. (6) (proof of Theorem 2)

import Mathlib
import Definitions.Def_LearnStability_ConvexSCO_Setting
import Definitions.Def_LearnStability_ConvexSCO_Problem

namespace LearnStability.ConvexSCO

/-- Eq. (6), proof of Theorem 2 (p. 2645): in a stochastic convex optimization problem whose
objective is `λ`-strongly convex (`λ > 0`) and `L`-Lipschitz in `h` on `H`, let `ĥ_S` minimize
the empirical risk `F_S` over `H` and let `ĥ_S^{(i)}` minimize the empirical risk of the sample
`S^{(i)}` obtained by replacing the `i`-th instance of `S` by `z'_i`. Then for every
`z ∈ Z`, `|f(ĥ_S, z) − f(ĥ_S^{(i)}, z)| ≤ 4L²/(λm)`. -/
theorem erm_replace_one_stability {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {Hset : Set E} {f : E → Z → ℝ} {L C lam : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (hlam : 0 < lam)
    (hsc : ∀ z, StrongConvexOn Hset lam (fun h => f h z))
    {m : ℕ} (hm : 1 ≤ m) (S : Fin m → Z) (i : Fin m) (z'_i : Z) {hS hSi : E}
    (hS_mem : hS ∈ Hset) (hS_min : ∀ h ∈ Hset, empRisk f S hS ≤ empRisk f S h)
    (hSi_mem : hSi ∈ Hset)
    (hSi_min : ∀ h ∈ Hset,
      empRisk f (Function.update S i z'_i) hSi ≤ empRisk f (Function.update S i z'_i) h) :
    ∀ z : Z, |f hS z - f hSi z| ≤ 4 * L ^ 2 / (lam * m) := by sorry

end LearnStability.ConvexSCO
