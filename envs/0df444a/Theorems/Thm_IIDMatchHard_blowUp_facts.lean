-- Prove2me | Theorems.Thm_IIDMatchHard_blowUp_facts
-- name    : IIDMatchHard.blowUp_facts
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:05:23.260789+00:00
-- url     : https://prove2.me/theorems/47879336-297d-4197-a26c-1647f568aef6
-- title:
--   Definition 3.7 and p.9 — vertices, edges, degree and max cut of the blow-up
-- statement:
--   Let $G$ be a finite simple graph with $n$ vertices, $m$ edges, largest degree $\Delta_G$ and maximum cut $C(G)$, and let $B\ge1$ be an integer. The blow-up $\tilde G$, with vertex set $V\times\{1,\dots,B\}$ and $(u,i)\sim(v,j)$ iff $(u,v)\in E$, satisfies
--
--   1. $|V(\tilde G)|=nB$;
--   2. $|E(\tilde G)|=mB^2$;
--   3. $\Delta_{\tilde G}=B\Delta_G$;
--   4. $C(\tilde G)=B^2C(G)$.
--
--   Blowing up multiplies the max-cut value by $B^2$, so approximating $C(\tilde G)$ is as hard as approximating $C(G)$, while the large graph makes adaptive policies concentrate.
--
--   Differences from the source:
--   - encoding: the blow-up is a simple graph; copies 1, …, B → a Mathlib SimpleGraph on V × Fin B (copies 0, …, B − 1); reason: simplicity holds by construction; same graph up to the index shift
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Definition 3.7 and the following paragraph, p.9 (PDF p.10)

import Definitions.Def_IIDMatchHard_Cut

set_option autoImplicit false

namespace IIDMatchHard

/-- **The blow-up facts** (after Definition 3.7). For an integer `B ≥ 1`, the blow-up `G̃` of
`G` is a simple graph with `nB` vertices, `mB²` edges, largest degree `∆_G̃ = B∆_G`, and max-cut
value `C(G̃) = B²C(G)`. Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), Definition 3.7 and the following paragraph, p.9 (PDF p.10).

**Formalization Note.** `G̃` is a `SimpleGraph` by construction, so "simple" needs no clause. -/
theorem blowUp_facts {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (B : ℕ)
    (hB : 1 ≤ B) :
    Fintype.card (V × Fin B) = Fintype.card V * B ∧
      numEdges (blowUp G B) = numEdges G * B ^ 2 ∧
      maxDeg (blowUp G B) = B * maxDeg G ∧
      maxCut (blowUp G B) = B ^ 2 * maxCut G := by sorry

end IIDMatchHard
