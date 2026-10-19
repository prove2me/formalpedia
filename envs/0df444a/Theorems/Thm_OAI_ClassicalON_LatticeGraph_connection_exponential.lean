-- Prove2me | Theorems.Thm_OAI_ClassicalON_LatticeGraph_connection_exponential
-- name    : OAI.ClassicalON.LatticeGraph.connection_exponential
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:54:57.748242+00:00
-- url     : https://prove2.me/theorems/3fb9cd1c-4a43-49b2-a556-afc9d64258c3
-- title:
--   Exponential decay of the bond-connection probability in OpenAI's bond representation, uniformly over lattice graphs and couplings in [0, β] (OpenAI classical O(n))
-- statement:
--   **Objects.** A `LatticeGraph` (published bundle `Def_ClassicalON`) is a finite set of sites in $\mathbb Z^2$ with a finite set of directed edges, each joining a site to its right or upper neighbour; `siteDistance` is the Euclidean distance between sites. For couplings $b$ on the edges, `G.connectionProbability b x y` (definitions bundle `OAIQWCO002` of this split) is the mean, under OpenAI's free bond measure `freeBondMean` with couplings $b$, of the indicator of `bondConnected … η x y`: every function in OpenAI's bond subspace of the bond configuration $\eta$ takes the same value at $x$ and $y$.
--
--   **Statement.** For every $\beta \ge 0$ there is $m > 0$ such that for every lattice graph $G$, all couplings $b$ with $0 \le b(e) \le \beta$, and all vertices $x, y$,
--   $$\mathrm{connectionProbability}_b(x, y) \;\le\; 4\,e^{-m\,|x - y|}.$$
--
--   Lean: `OAI.ClassicalON.LatticeGraph.connection_exponential`, OpenAI's theorem of that name.
-- source:
--   OpenAI, Exponential decay in two-dimensional classical O(n) models, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 215; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ClassicalON/CoarseExponential.lean (declaration OAI.ClassicalON.LatticeGraph.connection_exponential)

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
open scoped Classical
namespace ClassicalON

namespace LatticeGraph

theorem connection_exponential (β : ℝ) (hβ : 0 ≤ β) :
    ∃ m : ℝ,0 < m  ∧  ∀ (G : LatticeGraph) (b : G.edges → ℝ),(∀ e,0 ≤ b e  ∧  b e ≤ β) →
      ∀ x y : G.vertices,G.connectionProbability b x y ≤ 4*Real.exp (-m*siteDistance x.val y.val) := by
  sorry

end LatticeGraph
end ClassicalON

end

end OAI
end
