-- Prove2me | Theorems.Thm_NearLinearRSP_TwoResources_Supplement_ram_clock_table_construction
-- name    : NearLinearRSP.TwoResources.Supplement.ram_clock_table_construction
-- status  : Proved
-- author  : @k-variant
-- created : 2026-11-25T09:18:41.008715+00:00
-- url     : https://prove2.me/theorems/737466f9-acda-4bbb-b19d-febe87a3e73d
-- title:
--   Bounded RAM construction of a single multidimensional clock table
-- statement:
--   Fix a clock call for a directed restricted shortest-path instance with $k>0$ resources, $d>0$ clock coordinates, and positive grid width $q$. Suppose the input state contains the specified graph and clock data, the key, parameter, and heap regions satisfy the separation and capacity conditions, and the table's data cells are zero. Let $B=2^h$ be the heap capacity, $N$ the number of incident vertices, and $m$ the number of edges.
--
--   The finite table-building command produces the dynamic-programming table, including its values, ranks, and parent records. It preserves the designated memory and registers and leaves the address of the table end in its output register. If $S(k,d,q,B,N,m)$ is the specified cost bound for a single grid row, the number $u$ of instructions satisfies
--
--   $$
--   u\le 2d(4q+5)+d+32+(S(k,d,q,B,N,m)+2)q^d.
--   $$
--
--   The memory and register guarantees allow consecutive clock calls to share the graph and retain previously constructed tables.
-- source:
--   Vikrant Ashvinkumar, A Deterministic Near-Linear Time Approximation Algorithm for Restricted Shortest Paths in Directed Graphs, Theorem 2 (p. 3) and Appendix B (p. 14), extending Sections 4–6 (pp. 6–12).

import Definitions.Def_NearLinearRSP_TwoResources_Supplement_TableMachine

open NearLinearRSP.TwoResources NearLinearRSP.TwoResources.Supplement
open NearLinearRSP.TwoResources.Mission.Structured NearLinearRSP.TwoResources.Supplement.LayerRAM NearLinearRSP.TwoResources.Supplement.TableQuery

theorem NearLinearRSP.TwoResources.Supplement.ram_clock_table_construction {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (base map keys params height W P : ℕ)
    (site : Site A base map params (2^height) W) (keyStart : map+3*A.I.graph.n+A.I.graph.edges.length ≤ keys)
    (keyEnd : keys + (incidentVertices A.I).length ≤ params) (hdis : W + 2*2^height ≤ P) (hq : 0 < A.q) (hd : 0 < A.d)
    (s : Store) (h : TableInput A base map keys params (2^height) W P s)
    (blank : ∀ x, base+4 ≤ x → x < extent A base → s.nm x = 0 ∧ s.rm x = 0) :
    ∃ t n, Run (multiInput A.I ε) (buildTableCmd k A.d) s t n ∧ TableContext A base map keys params (2^height) W P t ∧
      TableImage A base (constructTable A) t ∧ TableFrame A base keys s t ∧ t.nr 203 = extent A base ∧
      (∀ a, TableOuter k a → GridFixed a → a ≠ 203 → t.nr a = s.nr a) ∧
      n ≤ tableCost k A.d A.q (2^height) (incidentVertices A.I).length A.I.graph.edges.length := by sorry
