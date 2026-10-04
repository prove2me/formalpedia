-- Prove2me | Theorems.Thm_MDPFinance_LPDuality_theorem_7_5_12
-- name    : MDPFinance.LPDuality.theorem_7_5_12
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:56:56.374048+00:00
-- url     : https://prove2.me/theorems/40dc7889-78c6-4f09-a478-acc8a4c93c8a
-- title:
--   Theorem 7.5.12 — an explicit error bound for grid-based value iteration
-- statement:
--   This closes the discretization program with a genuinely computable guarantee: iterating the grid
--   operator $T_G$ from any starting point $g$ approximates the true value function $J_\infty$ with
--   an explicit two-part error bound — a geometric term in the number of iterations (exactly Theorem
--   7.3.5's own convergence rate, chunk `07a`'s goal, applied now to $T_G$) plus a fixed discretization
--   bias $\|J_\infty - T_GJ_\infty\|_G$ that itself vanishes as the mesh is refined. Together with
--   Proposition 7.5.11, this is what makes state-space discretization a genuine numerical method with
--   a controllable, quantified error, not merely a heuristic.
--
--   **Moderation note.** $J_\infty$ is the model's value function (`hJ`), which the draft left as an arbitrary element of $IM_c$ named `Jinfty`. The remark "$\|J_\infty-T_GJ_\infty\|_G\to 0$ as the mesh size tends to zero" is no longer asserted: it rests on the linear-interpolation construction of $T_G$ ($T_GJ_\infty=J_\infty$ on the grid, interpolation between grid points within distance $h$, uniform continuity of $J_\infty$), which the abstract `GridApprox` does not carry, and for abstract grid data the draft's clause is false (take $T_G\equiv 0$).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 222, Theorem 7.5.12

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Value
import Definitions.Def_MDPFinance_LPDuality_Bounding
import Definitions.Def_MDPFinance_LPDuality_Discretization

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.LPDuality

/-- Theorem 7.5.12 (Bäuerle–Rieder, p. 222, PDF 233). Suppose that `\beta\alpha_G < 1`. Then it
holds for `g \in IM_c`: `\|J_\infty - T_G^ng\|_G \le \frac{1}{1-\beta\alpha_G}\big[(\beta
\alpha_G)^n\|T_Gg-g\|_G + \|J_\infty-T_GJ_\infty\|_G\big]`, where `\|J_\infty-T_GJ_\infty\|_G \to
0` if the mesh size `h` tends to zero. `T_G`'s own `\beta\alpha_G`-Lipschitz property
(`hTG_lip`) is taken as a hypothesis, standing for the Banach-fixed-point argument the book's own
proof of this theorem carries out on `T_G` exactly as Lemma 7.3.3 did on `T` — not re-derived
from the grid data itself, per `Def_..._Discretization.lean`'s docstring. `J_∞` is the model's
value function (`hJ`, real-valued in the contracting model). The remark "`\|J_\infty-T_GJ_\infty
\|_G \to 0` if the mesh size `h` tends to zero" is not asserted: it rests on the linear-interpolation
construction of `T_G` (`T_GJ_∞ = J_∞` on the grid, interpolation between grid points within
distance `h`, uniform continuity of `J_∞`), which the abstract `GridApprox` does not carry; for
abstract grid data it is false (e.g. `T_G ≡ 0`). -/
theorem theorem_7_5_12 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hαb : M.β * αb < 1)
    (IMc : Set (E → ℝ)) (G : GridApprox M IMc) (αG : ℝ) (hαG : M.β * αG < 1)
    (hTG_lip : ∀ v ∈ IMc, ∀ w ∈ IMc,
      normG G.bG (fun x => G.TG v x - G.TG w x) ≤ M.β * αG * normG G.bG (fun x => v x - w x))
    (Jinfty : E → ℝ) (hJ : ∀ x, Jinf M x = (Jinfty x : EReal)) (hJinftymem : Jinfty ∈ IMc)
    (g : E → ℝ) (hg : g ∈ IMc) :
    ∀ n : ℕ, normG G.bG (fun x => Jinfty x - (G.TG)^[n] g x) ≤
        (1 / (1 - M.β * αG)) * ((M.β * αG) ^ n * normG G.bG (fun x => G.TG g x - g x) +
          normG G.bG (fun x => Jinfty x - G.TG Jinfty x)) := by sorry

end MDPFinance.LPDuality
