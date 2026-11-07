-- Prove2me | Theorems.Thm_MinBisectFPT_lemma_4_6
-- name    : MinBisectFPT.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:32.377359+00:00
-- url     : https://prove2.me/theorems/b19251da-2aa1-4967-a333-82e99b6fe422
-- title:
--   Lemma 4.6 — Algorithm 1 computes the table in time $2^{O(k)}n^{O(1)}$
-- statement:
--   Under the standing assumptions of §4, given the tables of the children of $t$, Algorithm 1 computes the table $C_t$ in time $2^{O(k)}n^{O(1)}$.
--
--   Formally, one Turing machine and one constant work for all contexts: on input the graph, $k$, the bags $\beta(t),\sigma(t),\gamma(t)$, and $\sigma(c),\alpha(c)$ and the exact table of each child $c$, the machine outputs the exact table of $t$ within $c\,2^{ck}(n+1)^c$ steps.
--
--   Differences from the source:
--   - reading: "an algorithm … in time $2^{O(k)}n^{O(1)}$" → one bundled `TM2` machine `M` and one constant `c`, chosen before the instance, within `c * 2^(c*k) * (n+1)^c` steps; reason: the paper counts bit operations (p.15) and fixes no machine; a RAM of this cost runs on a `TM2` with polynomial overhead, and the bound is closed under polynomials; `n+1` because a machine still runs at `n = 0, 1`
--   - reading: "Algorithm 1 computes" → existence of a machine computing the table within the bound; reason: the steps that characterize Algorithm 1 are the correctness statements of Lemmas 4.2–4.5 and (4.1)
--   - encoding: input: "a node t of the decomposition, and the tables $C_c$ of its children" → the local data of the node, not the whole decomposition; reason: (D1)–(D3) do not bound the number of nodes, and a machine reads its whole input; the node's data is what the algorithm uses
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 4.6, p.14; Algorithm 1, p.15

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_MinBisectFPT_encodeNodeInput

open scoped Classical

namespace MinBisectFPT

/-- **Lemma 4.6.** Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 4.6, p.14: "Given the tables of the children of t, Algorithm 1 computes the
table C_t in time 2^{O(k)} n^{O(1)}."

**Formalization Note** One bundled Turing machine `M` and one constant `c` before the node, as in
Theorem 1.1; `M` receives the node's data and the children's tables. That `M` exists is the statement; the
correctness steps that characterize Algorithm 1 are Lemmas 4.2–4.5 and (4.1). -/
theorem lemma_4_6 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ), ∀ (n : ℕ) (ctx : NodeCtx n),
      HMBinPacking.OutputsWithin M (encodeNodeInput ctx.G ctx.D ctx.k ctx.t)
        (encodeTable ctx.G ctx.D ctx.k ctx.t) (c * 2 ^ (c * ctx.k) * (n + 1) ^ c) := by sorry

end MinBisectFPT
