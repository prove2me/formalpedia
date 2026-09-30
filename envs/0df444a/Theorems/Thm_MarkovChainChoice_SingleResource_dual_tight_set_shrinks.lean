-- Prove2me | Theorems.Thm_MarkovChainChoice_SingleResource_dual_tight_set_shrinks
-- name    : MarkovChainChoice.SingleResource.dual_tight_set_shrinks
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:17:27.694709+00:00
-- url     : https://prove2.me/theorems/c4c78635-4b1e-42f2-895a-5e95b4866e7c
-- title:
--   Lemma 3 — lowering all revenues by $\eta\ge0$ shrinks the dual tight set
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model with the standing assumptions, $r\in\mathbb R^n$ arbitrary revenues and $\eta\ge 0$. Let $\hat v^0$ be an optimal solution of (Dual) with revenues $r$, and let $\hat v^\eta$ be an optimal solution of (Dual) when the revenue of every product is decreased by $\eta$, i.e. with revenues $r_j-\eta$. Then
--   $$\{j\in N:\ \hat v^\eta_j=r_j-\eta\}\ \subseteq\ \{j\in N:\ \hat v^0_j=r_j\}.$$
--
--   Combined with Theorem 2, this says that decreasing all revenues by the same nonnegative amount makes the optimal assortment produced by the dual smaller. This is the step that turns monotonicity of marginal values into nested offer sets in Theorem 5.
--
--   **Formalization Note** The paper writes $\subset$ for (non-strict) inclusion; it is rendered as $\subseteq$. Both dual solutions are arbitrary optimal solutions. No sign condition is placed on $r$.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1327, Lemma 3

import Mathlib
import Definitions.Def_MarkovChainChoice_SingleResource_Assortment
open MarkovChainChoice.Shared

namespace MarkovChainChoice.SingleResource

theorem dual_tight_set_shrinks {n : ℕ} (M : Model n) (r : Fin n → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (v0 vη : Fin n → ℝ) (hv0 : IsDualOptimal M r v0)
    (hvη : IsDualOptimal M (fun j => r j - η) vη) :
    Finset.univ.filter (fun j => vη j = r j - η) ⊆
      Finset.univ.filter (fun j => v0 j = r j) := by sorry

end MarkovChainChoice.SingleResource
