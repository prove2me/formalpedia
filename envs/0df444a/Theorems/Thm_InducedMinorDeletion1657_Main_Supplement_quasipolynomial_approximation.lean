-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_Supplement_quasipolynomial_approximation
-- name    : InducedMinorDeletion1657.Main.Supplement.quasipolynomial_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:16:46.304424+00:00
-- url     : https://prove2.me/theorems/0479b933-f7d9-47be-9c0e-dc78ff9f1620
-- title:
--   Theorem 1.2 — quasipolynomial approximation scheme for hereditary MSO deletion
-- statement:
--   Fix a finite graph $H$, a nonnegative integer $t$ and a hereditary closed graph MSO sentence $\varphi$. For every fixed real $\varepsilon>0$ there exist one deterministic machine and positive natural constants $C,c$, chosen before every input graph $G$. On every $H$-induced-minor-free input with $n$ vertices, the machine receives only the graph and returns a feasible deletion set $S$ with
--   $$|S|\le(1+\varepsilon)|R|\quad\text{for every feasible set }R,$$
--   or reports failure exactly when no feasible set exists. It halts within
--   $$C\,2^{C(\log_2(n+2))^c}$$
--   steps. Feasibility means $\operatorname{tw}(G-S)\le t$ and $G-S\models\varphi$. The machine receives no optimum, modulator, decomposition or representation. The guarantee includes optimum zero and every positive accuracy, with no upper restriction on $\varepsilon$. This is the approximation companion to the exact algorithm in Theorem 1.1.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; reason: finite relabeling preserves every instance; the base nonnegative treewidth convention changes no nonnegative-width predicate
--   - reading: unqualified hereditary MSO formula → closed ordinary incidence MSO2, using the base syntax and satisfaction, with hereditariness under all finite induced-subgraph embeddings; reason: this is the same standard stronger MSO reading as the published goal; MSO1 embeds and no union-closure or satisfiability is imposed
--   - generalization: positive t in the numbered theorem because N = {1,2,...} → every nonnegative t; reason: for t = 0 use t′ = 1 and conjoin edgelessness with φ; this is hereditary and preserves feasible sets and optimum
--   - encoding: a quasipolynomial-time approximation scheme → for each ε > 0 one finite multi-stack Turing machine with time C*2^{C*(log₂(n+2))^c} and distinct failure/subset encodings; reason: Section 7 supplies exponent ten; existential positive C,c retain the claimed class, absorb polynomial simulation overhead, and cover small inputs
--   - encoding: a deletion set within (1+ε) times OPT → a feasible returned set compared with every feasible set, and failure exactly for infeasible inputs; reason: finite feasible families attain their optimum; explicit failure avoids assigning an optimum to an empty family
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 3 (PDF p. 4), Theorem 1.2; proof restated printed 30 / PDF 31; proof printed 31–33 / PDF 32–34

import Definitions.Def_InducedMinorDeletion1657_Main_Supplement_Approximation

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main.Supplement

/-- Theorem 1.2, printed p.3 / PDF p.4, with the abstract's nonnegative t.
At t=0 use t'=1 and conjoin edgelessness with φ; this preserves hereditariness. -/
theorem quasipolynomial_approximation :
  ∀ (H : InputGraph) (t : ℕ) (φ : Sentence), hereditary φ →
    ∀ ε : ℝ, 0 < ε →
      ∃ (A : Machine) (C c : ℕ), 0 < C ∧ 0 < c ∧
        ∀ G : InputGraph, excluded H.graph G.graph →
          ∃ o : Option (Finset (Fin G.n)), approxResult G t φ ε o ∧
            machineOutputs A (graphTape G) (answerTape o) (qpTime C c G.n) := by sorry

end InducedMinorDeletion1657.Main.Supplement
