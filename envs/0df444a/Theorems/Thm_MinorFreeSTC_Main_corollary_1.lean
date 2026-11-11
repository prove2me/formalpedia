-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_corollary_1
-- name    : MinorFreeSTC.Main.corollary_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:21:22.049517+00:00
-- url     : https://prove2.me/theorems/13858ec8-6837-4520-b86a-4186faf008f4
-- title:
--   Corollary 1 — some universal c₀ ≥ 1 gives P-tiled ∆-radius ∆/(2r)-buffered (r−1)-width cop decompositions for tiles of diameter ≤ ∆/(c₀ r log n), poly-time w.h.p.
-- statement:
--   There is a universal constant $c_0\ge1$ for which the following holds (this is $\mathrm{CopConstant}(c_0)$): let $\Delta>0$, let $G$ be a connected $K_r$-minor-free weighted graph on $n\ge1$ vertices (weights in $[1,n^k]$), and let $\mathcal P$ be a partition of $V$ into parts of strong diameter at most $\delta$, where
--   $$\delta\le\frac{\Delta}{c_0\cdot r\cdot\log_2 n}.$$
--   Then **(E)** $G$ admits a $\mathcal P$-tiled $\Delta$-radius $\Delta/(2r)$-buffered $(r-1)$-width buffered cop decomposition, and **(A)** for every $c>1$ one admissible program computes such a decomposition from $(G,\Delta,r,\mathcal P)$ in at most $Cn^K+C$ steps ($C,K$ depending on $r,k,c$), failing on a set of coin tapes of measure at most $n^{-c}$.
--
--   It is a reparametrization of Theorem 8 and supplies the tiled cop decompositions of Lemma 12; the constant $c_0$ reappears in Lemma 12 and Theorem 9.
--
--   Differences from the source:
--   - reading: 'there is a polynomial time algorithm that with high probability returns such decomposition' → for every c > 1 one program of the machine `Program` (the published SmaleNinth real-RAM core plus a fair `coin` and `roundUpPow`, rational literals), fixed before r, ϵ and the graph, every run of which halts within C·n^K + C steps (C, K depending only on the parameters named in the statement) and whose failure set of coin tapes has measure ≤ n^{−c}; reason: the paper names no machine; §9.2 (p. 53) lists the assumed operations, and p. 13 defines 'with high probability' as probability ≥ 1 − n^{−c} for a constant c that can be made arbitrarily large
--   - encoding: δ ≤ ∆/(c₀·r·log n) → δ·(c₀·r·log₂ n) ≤ ∆; reason: avoids Lean's division by zero at n = 1, where the source's bound is ∞
--   - encoding: graph (with the standing assumption 'we will assume all input graphs are connected', p. 14) → hypothesis `Connected G` (d_G(u, v) < ∞ for all u, v); reason: standing assumption of §3.1 made explicit
--   - encoding: 'we will assume … w(e) ∈ [1, poly(n)]' (p. 13, standing for §§4–9.1) → hypothesis `AspectBounded G k` (1 ≤ w(e) ≤ n^k) for an arbitrary k : ℕ; running-time constants may depend on k; reason: standing assumption of §3.1 made explicit; §9.2 removes it only for the final theorem
--   - encoding: n-node graph → `[Nonempty V]` (n ≥ 1); reason: log n, log log n and n^{−c} are undefined or degenerate at n = 0
--   - encoding: log → `Real.logb 2` (Lean's `logb 2 0 = 0` gives log 0 a value at n = 1); reason: p. 13: all logarithms are base 2
--   - encoding: distances d_G, d_C, d_T and α·d_G(u, v) → values in [0, ∞] (`ℝ≥0∞`), α·d as `ENNReal.ofReal α * d`; reason: the published `WGraph.dist`/`distIn` convention; on connected graphs and connected clusters every distance is finite
--   - encoding: the graph (and parameters) given to the algorithm; its output → input cells `E.cells` ([n, m, then each listed edge as endpoint numbers and weight], for every enumeration and edge order `E : Encoding G`) followed by the parameters; output read from the memory block named by pointers p[1], p[2] in the layout of the corresponding `…Out` predicate; reason: a machine needs a concrete layout; quantifying over every encoding means the algorithm cannot exploit a convenient order
--   - encoding: the partition P handed to the algorithm; the decomposition returned → a vertex labelling of P; three cells per vertex (supernode root, parent supernode root, skeleton parent) as in `CopOut`; reason: a concrete layout
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 22, Corollary 1

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_MinorFreeSTC_Main_CopConstant

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-- **Corollary 1** (p. 22). There is a universal constant `c₀ ≥ 1` for which the statement of
Corollary 1 holds (`CopConstant c₀`: tiled buffered cop decompositions exist for tiles of
diameter at most `∆/(c₀ r log n)`, and are computed with high probability in polynomial time). -/
theorem corollary_1 : ∃ c₀ : ℝ, 1 ≤ c₀ ∧ CopConstant c₀ := by sorry

end MinorFreeSTC.Main
