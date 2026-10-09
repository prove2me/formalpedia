-- Prove2me | Theorems.Thm_OnlineCRS_Matroid_base_maximal
-- name    : OnlineCRS.Matroid.base_maximal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:23:08.143743+00:00
-- url     : https://prove2.me/theorems/9272380c-b1bd-4b4f-96d1-24332899e890
-- title:
--   §2.1.1, p. 11 — P_B is the set of maximal vectors of P_F, and every point of P_F lies below one
-- statement:
--   Let $M$ be a matroid on the finite ground set $N$ with rank function $\operatorname{rank}$, let
--   $P_{\mathcal F}=\{x\in\mathbb R^N_{\ge0} : x(S)\le\operatorname{rank}(S)\ \forall S\subseteq N\}$ be its matroid polytope and
--   $P_{\mathcal B}=\{x\in P_{\mathcal F} : x(N)=\operatorname{rank}(N)\}$ its base polytope. Then
--
--   1. $P_{\mathcal B}$ is the set of all maximal vectors of $P_{\mathcal F}$:
--   $$P_{\mathcal B}=\{x\in P_{\mathcal F} : \text{for all } y\in P_{\mathcal F},\ x\le y \text{ coordinatewise implies } y=x\};$$
--   2. every $x\in P_{\mathcal F}$ is dominated coordinatewise by some $y\in P_{\mathcal B}$.
--
--   Together with the monotonicity of the set $S$ in $x$, the second part is what makes it safe, in the termination analysis of the chain construction, to assume $x\in b\cdot P_{\mathcal B}$ instead of $x\in b\cdot P_{\mathcal F}$ (scale by $b\ge0$).
--
--   **Formalization Note** The ground set is the whole finite type ($M.E=$ univ). Part 2 is the consequence of part 1 that the paper's "it is safe to assume" uses; it is stated explicitly because maximal elements of $P_{\mathcal F}$ exist only by compactness.
-- source:
--   arXiv:1508.00142v2, §2.1.1, p. 11, first paragraph, second sentence

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Polytope

namespace OnlineCRS.Matroid

/-- arXiv:1508.00142v2, §2.1.1, p. 11, first paragraph, second sentence: the base polytope `P_B` is the
set of all maximal vectors of `P_F`, and every point of `P_F` lies coordinatewise below a point of `P_B`
(which is what makes it "safe to assume that `x ∈ b · P_B`"). -/
theorem base_maximal {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ) :
    basePolytope M =
        {x | x ∈ matroidPolytope M ∧
          ∀ y ∈ matroidPolytope M, (∀ e, x e ≤ y e) → y = x} ∧
      ∀ x ∈ matroidPolytope M, ∃ y ∈ basePolytope M, ∀ e, x e ≤ y e := by sorry

end OnlineCRS.Matroid
