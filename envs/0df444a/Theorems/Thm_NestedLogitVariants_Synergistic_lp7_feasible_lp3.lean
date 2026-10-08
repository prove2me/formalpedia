-- Prove2me | Theorems.Thm_NestedLogitVariants_Synergistic_lp7_feasible_lp3
-- name    : NestedLogitVariants.Synergistic.lp7_feasible_lp3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:43:13.775984+00:00
-- url     : https://prove2.me/theorems/62bddf76-cf85-4113-907f-63cdc3fc3678
-- title:
--   §4.2, p. 20 — every feasible solution of problem (7) is feasible for problem (3)
-- statement:
--   Consider an instance of the nested logit assortment problem with fully-captured nests, $v_{i0} = 0$ for every nest $i$. If $(x, y)$ is feasible for problem (7), that is,
--
--   $$v_0 x \ge \sum_{i\in M} y_i, \qquad y_i \ge \Big(\sum_{j \in N} v_{ij} z_{ij}\Big)^{\gamma_i}\left[\frac{\sum_{j\in N} r_{ij} v_{ij} z_{ij}}{\sum_{j\in N} v_{ij} z_{ij}} - x\right] \quad \forall z_i \in [0,1]^n,\ i \in M,$$
--
--   then $(x, y)$ is feasible for problem (3):
--
--   $$v_0 x \ge \sum_{i \in M} y_i, \qquad y_i \ge V_i(S_i)^{\gamma_i}\,(R_i(S_i) - x) \quad \forall S_i \subseteq N,\ i \in M.$$
--
--   Problem (3) is thus a relaxation of problem (7); feasibility for (7) is what the proof of Theorem 7 establishes.
--
--   **Formalization Note** The standing assumptions are those of the model (see the Model definition) and of §4: every nest is fully captured, $v_{i0} = 0$, and $\gamma_i > 1$ for some nest $i$ (p. 16). The hypothesis $\gamma_i > 1$ for some $i$ is not used by this statement but is kept as the section's standing assumption.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 20, §4.2 (paragraph after display (7))

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Relaxation

namespace NestedLogitVariants.Synergistic

/-- §4.2, p. 20: problem (3) is a relaxation of problem (7); every feasible solution `(x, y)` of (7)
is feasible for (3). (Fully-captured nests, `v_{i0} = 0`, as throughout §4.) -/
theorem lp7_feasible_lp3 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i) :
    ∀ x (y : ι → ℝ), LP7Feasible I x y → LP3Feasible I x y := by sorry

end NestedLogitVariants.Synergistic
