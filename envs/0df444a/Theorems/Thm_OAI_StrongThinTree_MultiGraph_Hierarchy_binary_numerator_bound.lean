-- Prove2me | Theorems.Thm_OAI_StrongThinTree_MultiGraph_Hierarchy_binary_numerator_bound
-- name    : OAI.StrongThinTree.MultiGraph.Hierarchy.binary_numerator_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T17:07:42.917166+00:00
-- url     : https://prove2.me/theorems/06fc19ec-b0b8-44bc-87e9-9f81d2bc3ea0
-- title:
--   Boundary-numerator bound for a contracted 0/1 embedding over a vertex hierarchy (OpenAI strong thin tree)
-- statement:
--   Let $G$ be a `MultiGraph n m`: $n$ vertices `Fin n`, $m$ edges `Fin m`, each edge $e$ with endpoints `left e` $\ne$ `right e`. For an edge set $T$ and a vertex set $S$, $\delta_T(S)$ (`cut T S`) is the set of edges of $T$ with exactly one endpoint in $S$. Let $H$ be a `Hierarchy n`: a finite family `nodes` of nonempty vertex sets that contains the whole vertex set and every singleton and is laminar (any two members are nested or disjoint), with a map `parent` that sends each member $A$ other than the whole vertex set to a member strictly containing $A$ and contained in every member strictly containing $A$. For a vertex set $A$, let $\partial A$ (`parentBoundary G A`) be the set of edges with both endpoints in `parent A` and exactly one endpoint in $A$.
--
--   Let $q, L, R$ be positive natural numbers, $M$ a set of members of $H$ none of which is the whole vertex set, and $\alpha, \varepsilon, \rho$ real numbers with $0 < \alpha \le 1$, $0 < \varepsilon < 1/3$ and $0 < \rho \le 1/1536$. Write $g = $ `truncationGain α` $= 1/(4b^4)$, where $b = $ `truncationBins α` $= 1 + \lceil \log_2(256/\alpha^2) \rceil$ (natural-number ceiling), and $s = \alpha g/32$; powers $s^{\varepsilon}$ and $s^{1+2\varepsilon}$ are real powers. Assume:
--   - $G$ is $q$-edge-connected: $|\delta_G(S)| \ge q$ for every nonempty proper vertex set $S$ (`EdgeConnected`);
--   - $H$ is locally $q$-connected in $G$ (`LocallyConnectedReal`): for every member $A$ of $H$ and every nonempty $S \subsetneq A$, at least $q$ edges with both endpoints in $A$ have exactly one endpoint in $S$;
--   - $s^{\varepsilon} \le 1/(1728 \cdot 1024/\varepsilon^2)$ and $6144/q \le s^{1+2\varepsilon}$;
--   - $q\rho\,|\delta_G(t)| \le |\partial t|$ for every $t \in M$;
--   - $\log_2(16/(\alpha g)) + 1 < L$ and $\log_2(24/(\rho s^2)) < R$.
--
--   Let $h$ be a natural number, $X$ an $h \times n$ real matrix with every entry $0$ or $1$, and $U$ an $m \times h$ real matrix with $U^{\mathsf T} U \le I$ in the Loewner order ($I - U^{\mathsf T}U$ positive semidefinite). Let $B$ be the $n \times m$ incidence matrix, $B_{ve} = $ `incidence e v`, where `incidence e` is the indicator of `left e` minus the indicator of `right e`, and let $W = UXB$. If $W_{ee} \ge 0$ for every edge $e$, then
--   $$\sum_{t \in M} \frac{\Bigl(\sum_{e \in \partial t} W_{ee}\Bigr)^2}{|\partial t|} \;\le\; c \cdot \sum_{e} \sum_{i} (XB)_{ie}^2, \qquad c = 2\alpha + \frac{2RL}{\dfrac{q}{8192} \cdot \dfrac{s^{\varepsilon}}{6912 \cdot 1024/\varepsilon^2} \cdot g},$$
--   where $c$ is `shortcutCoefficient q L R α ε` and a term with $|\partial t| = 0$ is $0$ (Lean's division by zero).
--
--   Lean: `OAI.StrongThinTree.MultiGraph.Hierarchy.binary_numerator_bound`, OpenAI's lemma of that name (in `lean/OAI/Combinatorics/ThinTrees/ShortcutDuality.lean`). `MultiGraph`, `cut` and `EdgeConnected` come from the published bundle `Def_StrongThinTree`; `Hierarchy`, `parentBoundary`, `LocallyConnectedReal`, `incidence`, `truncationGain` and `shortcutCoefficient` from the definitions bundle `OAIQWSTT000` of this split.
-- source:
--   OpenAI, The strong thin tree conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-strong-thin-tree-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ThinTrees/ShortcutDuality.lean (declaration OAI.StrongThinTree.MultiGraph.Hierarchy.binary_numerator_bound)

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

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset StrongThinTree.Geometry
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {n m h : ℕ} (G : MultiGraph n m)

namespace Hierarchy
variable {G : MultiGraph n m} {H : Hierarchy n}

lemma binary_numerator_bound {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hconn : H.LocallyConnectedReal G q)
    (M : Finset (Finset (Fin n))) (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ M, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (H.parentBoundary G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R)
    (X : Matrix (Fin h) (Fin n) ℝ) (hX : ∀i v, X i v=0 ∨ X i v=1)
    (U : Matrix (Fin m) (Fin h) ℝ) (hU : Uᵀ*U ≤ 1)
    (hpositive : ∀e, 0 ≤ (U*(X*Matrix.of (fun v e => G.incidence e v))) e e) :
    (∑t : M, (∑e ∈ H.parentBoundary G t, (U*(X*Matrix.of (fun v e => G.incidence e v))) e e)^2/
      ((H.parentBoundary G t).card : ℝ)) ≤
      shortcutCoefficient q L R α ε*(∑e, ∑i, (X*Matrix.of (fun v e => G.incidence e v)) i e ^2) := by
  sorry

end Hierarchy
end
end StrongThinTree.MultiGraph

end

end OAI
end
