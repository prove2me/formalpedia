-- Prove2me | Theorems.Thm_GeomRescale_greedy_min
-- name    : GeomRescale.greedy_min
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:05.642245+00:00
-- url     : https://prove2.me/theorems/b7f4df73-af23-4101-8971-a4e83d1e23c1
-- title:
--   Displays (2)–(3): $\mathrm{GreedyMin}$ is optimal
-- statement:
--   Let $f : 2^V \to \mathbb{R}$ be submodular with $f(\emptyset) = 0$, let $w : V \to \mathbb{R}$, and let $v_1, \dots, v_n$ be an order with $w(v_1) \le \dots \le w(v_n)$. Then the vector $x$ of (2), defined by $x(v_i) = f(\{v_1, \dots, v_i\}) - f(\{v_1, \dots, v_{i-1}\})$, is an optimal solution of $\min\{w^{\mathsf T} x : x \in B(f)\}$, and
--
--   $$\min_{x \in B(f)} w^{\mathsf T} x = \sum_{i=1}^{n-1} f(\{v_1, \dots, v_i\})(w(v_i) - w(v_{i+1})) + f(V) w(v_n).$$
--
--   This is the separation step of Algorithm 1, and the formula drives Lemma 3.3.
--
--   Differences from the source:
--   - encoding: ground set $V$ with $n$ elements → `Fin (m + 1)`, an order as a position map; reason: $v_n$ needs $n \ge 1$; same instances
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, displays (2)–(3), p.4

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_IsSortedBy
import Definitions.Def_GeomRescale_pref

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace GeomRescale

/-- `GreedyMin(f, w)` is optimal, and the optimal value is (3) (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, displays (2)–(3), p.4): for an
order `v₁, …, v_n` with `w(v₁) ≤ … ≤ w(v_n)`, the vector `x` of (2) lies in `B(f)`, minimizes `wᵀx`
over `B(f)`, and
`min_{x ∈ B(f)} wᵀx = ∑_{i=1}^{n−1} f({v₁, …, v_i})(w(v_i) − w(v_{i+1})) + f(V) w(v_n)`.

**Formalization Note.** `n = m + 1`, so that `v_n` exists. The vector (2) is the published
`SchrijverSFM.Alg.greedy f σ`, with `v_{i+1} = σ⁻¹(i)`. -/
theorem greedy_min {m : ℕ} (f : Finset (Fin (m + 1)) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (w : Fin (m + 1) → ℝ) (σ : Equiv.Perm (Fin (m + 1))) (hσ : IsSortedBy w σ) :
    greedy f σ ∈ baseB f ∧
      (∀ x ∈ baseB f, w ⬝ᵥ greedy f σ ≤ w ⬝ᵥ x) ∧
      w ⬝ᵥ greedy f σ =
        ∑ i : Fin m, f (pref σ ((i : ℕ) + 1)) * (w (σ.symm i.castSucc) - w (σ.symm i.succ)) +
          f Finset.univ * w (σ.symm (Fin.last m)) := by sorry

end GeomRescale
