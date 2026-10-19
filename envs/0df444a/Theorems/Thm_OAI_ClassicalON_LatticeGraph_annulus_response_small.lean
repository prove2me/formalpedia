-- Prove2me | Theorems.Thm_OAI_ClassicalON_LatticeGraph_annulus_response_small
-- name    : OAI.ClassicalON.LatticeGraph.annulus_response_small
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:54:51.829431+00:00
-- url     : https://prove2.me/theorems/afaaef4f-baba-4ebb-b3d4-0ca01159207e
-- title:
--   The second-axis response of the O(3) model across a dyadic annulus is small at large scales, uniformly in the boundary pins (OpenAI classical O(n))
-- statement:
--   **Objects.** A `LatticeGraph` (published bundle `Def_ClassicalON`) is a finite set of sites in $\mathbb Z^2$ with directed edges to right or upper neighbours; `Spin 3` is the unit sphere of $\mathbb R^3$. The following are from the definitions bundle `OAIQWCO002` of this split. `G.WithinDyadicBox k` says every vertex has both coordinates of absolute value at most $2\cdot 2^k$. With `scaledSite k x` $= x/2^k$, `G.BoundaryPins k 3 P` says every pinned vertex ($P(x) = \text{some}\ s$) has its scaled site in the square $[-1,1]^2$ or outside the open square $(-2,2)^2$. `G.spinSystem 3 b P` is the O(3) spin system on $G$ with couplings $b$ and pins $P$, with Gibbs average `average` (weight $\exp(\sum_e b(e)\langle\sigma_{\mathrm{left}(e)}, \sigma_{\mathrm{right}(e)}\rangle)$). For edge functions $h, k$, `secondAxisResponse h k` is the Gibbs average of $\mathrm{energy}(hk\,C^2) + \mathrm{energy}(h\,C)\,\mathrm{energy}(k\,C)$ for OpenAI's rotation generator `axisC` $= C$, and `G.thetaEdge k` is the edge difference of OpenAI's cutoff function `squareTheta` at scale $2^k$.
--
--   **Statement.** For all $\beta \ge 0$ and $\varepsilon > 0$ there is $k \ge 4$ such that for every lattice graph $G$ within the dyadic box of size $k$, all couplings $b$ with $0 \le b(e) \le \beta$, and all pins $P$ satisfying `BoundaryPins k 3 P`,
--   $$-\,\mathrm{secondAxisResponse}\bigl(\theta_k, \theta_k\bigr) \;\le\; \varepsilon, \qquad \theta_k = \mathrm{thetaEdge}\ k.$$
--
--   Lean: `OAI.ClassicalON.LatticeGraph.annulus_response_small`, OpenAI's theorem of that name.
-- source:
--   OpenAI, Exponential decay in two-dimensional classical O(n) models, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 215; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ClassicalON/AnnulusSmall.lean (declaration OAI.ClassicalON.LatticeGraph.annulus_response_small)

import Mathlib
import Definitions.Def_ClassicalON
import Definitions.Def_OAIQWCO002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
namespace ClassicalON
namespace LatticeGraph

theorem annulus_response_small (β : ℝ) (hβ : 0 ≤ β) (ε : ℝ) (hε : 0<ε) :
    ∃ k : ℕ, 4 ≤ k ∧ ∀ (G : LatticeGraph), G.WithinDyadicBox k →
      ∀ (b : G.edges → ℝ), (∀ e,0 ≤ b e ∧ b e ≤ β) →
      ∀ (P : G.vertices → Option (Spin 3)), G.BoundaryPins k 3 P →
      -(G.spinSystem 3 b P).secondAxisResponse (G.thetaEdge k) (G.thetaEdge k) ≤ ε := by
  sorry

end LatticeGraph
end ClassicalON

end

end OAI
end
