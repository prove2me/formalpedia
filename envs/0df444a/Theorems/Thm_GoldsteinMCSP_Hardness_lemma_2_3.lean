-- Prove2me | Theorems.Thm_GoldsteinMCSP_Hardness_lemma_2_3
-- name    : GoldsteinMCSP.Hardness.lemma_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T17:12:56.449878+00:00
-- url     : https://prove2.me/theorems/6c3c9482-0ada-47b2-a321-dcdf041d7136
-- title:
--   Lemma 2.3 — exact cubic-graph gadget correspondence
-- statement:
--   Let G be any finite simple undirected cubic graph with N vertices, and let h be a nonnegative integer. Construct the fully modified multiset instance I_G by equations (3) and (4), orienting edges by the cycle-and-forest rule on page 7 with fixed vertex-order tie choices. Then
--
--   $$\text{G has an independent set of size }h\quad\Longleftrightarrow\quad\exists\text{ a common partition of }I_G\text{ with block count }m\text{ satisfying }m+h=12N.$$
--
--   In the right-hand side, m is the number of blocks of the common partition: equivalently its size is exactly 12N−h. Both directions concern arbitrary feasible solutions, not only optimal ones. The empty graph is allowed and has the empty common partition, so the equivalence holds there exactly for h=0.
--
--   Differences from the source:
--   - encoding: a cubic graph on N vertices and arbitrary choices in the construction → a SimpleGraph on Fin N with decidable adjacency and fixed executable vertex-order choices; reason: finite relabelling and deterministic tie choices retain every cubic input
--   - encoding: partition size 12N − h → partition size + h = 12N for natural h; reason: addition expresses the exact size relation without spurious solutions caused by truncated subtraction
--   - encoding: multisets of strings over fresh letters → indexed component lists with labels 10u+j, preserving multiplicity; reason: component order is bookkeeping; every component is cut separately and all blocks are matched by permutation
-- source:
--   Goldstein, Kolman and Zheng (2005), Minimum Common String Partition Problem: Hardness and Approximations, EJC 12, R50, DOI 10.37236/1947, Lemma 2.3, printed p. 8 (PDF p. 8)

import Definitions.Def_GoldsteinMCSP_Hardness_Gadget

namespace GoldsteinMCSP.Hardness

theorem lemma_2_3 {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hc : cubic G) (h : ℕ) :
    (∃ s : Finset (Fin N), independent G s ∧ s.card = h) ↔
    (∃ p q : List Word, familyCommon (gadgetInstance G).1 (gadgetInstance G).2 p q ∧
      p.length + h = 12*N) := by sorry

end GoldsteinMCSP.Hardness
