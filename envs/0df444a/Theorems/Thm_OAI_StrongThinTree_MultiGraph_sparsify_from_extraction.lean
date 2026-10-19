-- Prove2me | Theorems.Thm_OAI_StrongThinTree_MultiGraph_sparsify_from_extraction
-- name    : OAI.StrongThinTree.MultiGraph.sparsify_from_extraction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T17:08:00.471659+00:00
-- url     : https://prove2.me/theorems/e5b722f8-5abf-4187-a78d-b6b1c0956375
-- title:
--   A tree packing of low-resistance edges yields an edge set packing stepCount r spanning trees and meeting each cut in at most a (1/2 + 3 splitTau r) fraction (OpenAI strong thin tree)
-- statement:
--   Let $G$ be a `MultiGraph n m` with $n \ge 2$: $n$ vertices `Fin n`, $m$ edges `Fin m`, each edge $e$ with endpoints `left e` $\ne$ `right e`. For an edge set $T$ and a vertex set $S$, $\delta_T(S)$ (`cut T S`) is the set of edges of $T$ with exactly one endpoint in $S$. An edge set $T$ is a spanning tree (`SpanningTree`) if every nonempty proper vertex set is crossed by an edge of $T$ and this fails after removing any one edge of $T$; $T$ packs $k$ trees (`TreePackable T k`) if it contains $k$ pairwise disjoint spanning trees.
--
--   For a natural number $r$ let $u_r = r^{-1/16}$ (`errorU r`), $t_r = r^{-1/2}$ (`resistanceT r`), $Q_r = \lfloor (1 - r^{-1/16})\,r \rfloor$ (`extractQ r`), $\varepsilon_r = 6t_r$ (`splitEpsilon r`), $\tau_r = 2\sqrt{\varepsilon_r} + \varepsilon_r$ (`splitTau r`) and $k_r = \lfloor (1 - 4u_r)\,r/2 \rfloor$ (`stepCount r`), all floors natural-number floors. Assume `StepNumeric r`, that is: $4 \le r$; $u_r \le 1/16$; $0 < Q_r$; $(1 + u_r)/Q_r \le 2t_r$; $\tau_r \le u_r/2$; $k_r \le \lfloor (1/2 - \tau_r)\,Q_r/(1 + u_r) \rfloor$; $\tfrac{5}{16} r \le k_r$; $k_r \le r/2$; and $(1/2 + 3\tau_r)\,r \le (1 + 15u_r)\,k_r$.
--
--   For an edge $e$ let $b_e$ (`incidence e`) be the indicator of `left e` minus the indicator of `right e`, let $\Lambda = \sum_{e} b_e b_e^{\mathsf T}$ be the Laplacian of all edges, and let $\mathbf 1_S$ be the indicator vector of a vertex set $S$. Let $X$ be an $n \times n$ real matrix in `matrixDomain G`: $\Lambda + \frac1n I \le X$ in the Loewner order, and $\mathbf 1_S^{\mathsf T} X \mathbf 1_S \le 3\,|\delta_G(S)|$ for every nonempty proper vertex set $S$. The resistance of an edge is $\mathrm{res}_X(e) = b_e^{\mathsf T} X^{-1} b_e$ (`resistance X e`, with Lean's matrix inverse). Assume the edges of resistance at most $4t_r$ (`thresholdEdges (resistance X) (4 * resistanceT r)`) pack $Q_r$ trees. Then there is an edge set $A$ that packs $k_r$ trees and satisfies
--   $$|\delta_A(S)| \;\le\; \Bigl(\frac12 + 3\tau_r\Bigr)\,|\delta_G(S)| \qquad \text{for every nonempty proper vertex set } S.$$
--
--   Lean: `OAI.StrongThinTree.MultiGraph.sparsify_from_extraction`, OpenAI's lemma of that name (in `lean/OAI/Combinatorics/ThinTrees/SparsifyGeometry.lean`). `MultiGraph`, `cut` and `SpanningTree` come from the published bundle `Def_StrongThinTree`; `StepNumeric`, `matrixDomain`, `resistance`, `thresholdEdges`, `TreePackable`, `incidence`, `extractQ`, `resistanceT`, `errorU`, `splitEpsilon`, `splitTau` and `stepCount` from the definitions bundle `OAIQWSTT000` of this split.
-- source:
--   OpenAI, The strong thin tree conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-strong-thin-tree-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ThinTrees/SparsifyGeometry.lean (declaration OAI.StrongThinTree.MultiGraph.sparsify_from_extraction)

import Mathlib
import Definitions.Def_StrongThinTree
import Definitions.Def_OAIQWSTT000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

lemma sparsify_from_extraction (hn : 2 ≤ n) {r : ℕ} (hnum : StepNumeric r)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ G.matrixDomain)
    (hp : G.TreePackable (G.thresholdEdges (G.resistance X) (4*resistanceT r)) (extractQ r)) :
    ∃A : Finset (Fin m), G.TreePackable A (stepCount r) ∧
      ∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
        ((G.cut A S).card:ℝ) ≤ (1/2+3*splitTau r)*(G.cut univ S).card := by
  sorry

end StrongThinTree.MultiGraph

end
end

end OAI
end
