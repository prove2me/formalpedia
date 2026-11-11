-- Prove2me | Theorems.Thm_FullImmersionFPT_Main_proposition_63
-- name    : FullImmersionFPT.Main.proposition_63
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:49:24.441211+00:00
-- url     : https://prove2.me/theorems/856728af-06b1-4f1a-b328-a9838c094821
-- title:
--   Proposition 63 — the folio P(G) in O(n⁵) time
-- statement:
--   Let $\delta_0\in\mathbb N$ and let $\mathcal G$ be a colorless decorated graph (labels in $\mathbb F_2^U$, no parent edge). Its folio $P(\mathcal G)$ — the colorless decorated graphs $\mathcal F$, up to equivalence, with at most $\delta_0$ vertices that $\mathcal G$ fully immerses — can be computed in time
--   $$O_{\delta_0,|U|}(n^5).$$
--   Formally: one program $P$ (input: the code of $\mathcal G$ and $\delta_0$) and for all $\delta_0,|U|$ a constant $c$ with $P$ outputting $P(\mathcal G)$ within $c\,n^5+c$ steps. It is the dynamic programming over the 2-edge cuts of $\mathcal G$ that removes 4-edge-connectivity from Proposition 24.
--
--   Differences from the source:
--   - generalization: §19 context: G an arbitrary colorless decorated graph with, "we may assume", ρ(R) ⊆ [δ0], and δ0 := |V(H)| fixed throughout the section → every colorless decorated graph G (no condition on its root values) and one program uniform in δ0 (δ0 is part of the input); reason: specializes to the section's setting; the WLOG on root values is not a hypothesis of the folio, and the uniform program is what Theorem 1 needs
--   - reading: "we can find/compute/test … in time O_{δ0,|U|}(n⁵)" → one program P of the published TrulySubcubicAPSP word RAM and a word-size factor b, fixed before every input, with c chosen after δ0 and |U|; on every input and every word size W ≥ b(⌊log₂(N+2)⌋+1) (FOMCMonDep.WordSizeOK, N = input length plus largest absolute entry) P halts within the explicit bound with a correct output; reason: the paper fixes a RAM storing graphs as adjacency lists of half-edges with constant-time access (p. 15) but names no formal machine; unit-cost word RAM with logarithmic words is the reading; each O(·) is an explicit constant chosen after the parameters it is subscripted with
--   - encoding: colorless decorated graphs → decorated graphs with q = 0 colors; reason: all color sets are empty either way
--   - encoding: decorated graphs (G, λ, R, ρ, α) over F₂^U with q colors → Decorated V H d q with labels Fin d → ZMod 2 (d = |U|), root : V → Option ℕ, colors Finset (Fin q); inputs as DecoCode edge lists; reason: Lean convention; every decorated graph is isomorphic to a code
--   - encoding: "the … folio of G can be computed/found" → the output cells hold a list of decorated-graph codes, each in the folio, such that every member of the folio (on any types) is equivalent to a listed one; reason: folios are sets of decorated graphs up to equivalence; duplicates are harmless
--   - encoding: graphs with loops and parallel edges, edges {h₁, h₂} of half-edges (§5) → Multigraph V H: finite vertex and half-edge sets in ambient types, inc, mate; an edge is s(h, mate h) : Sym2 H; a trail is the list of the tail half-edges of its arcs; reason: the paper's half-edge model; keeping the ambient types fixed lets splitting off delete vertices and half-edges
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 75, Proposition 63 (folio defined p. 71)

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_Decorated

set_option autoImplicit false

open Classical

namespace FullImmersionFPT.Main

/-- **Proposition 63** (p. 75). One program `P` computes the folio `P(G)` of a colorless decorated
graph `G` (the colorless decorated graphs with at most `δ₀` vertices that `G` fully immerses, up to
equivalence) within `c · n⁵ + c` steps, `c` depending only on `δ₀` and `|U|`. -/
theorem proposition_63 :
    ∃ (P : List TrulySubcubicAPSP.Instr) (b : ℕ), ∀ δ₀ d : ℕ, ∃ c : ℕ,
      ∀ (n m : ℕ) (K : DecoCode n m d 0), K.toDeco.IsDecorated → ∀ W : ℕ,
        FOMCMonDep.WordSizeOK b (K.words ++ [(δ₀ : ℤ)]) W →
        RunsWithin P W (c * n ^ 5 + c) (K.words ++ [(δ₀ : ℤ)]) fun out =>
          EmitsUpToEquiv out fun F => Decorated.InFolio δ₀ K.toDeco F := by sorry

end FullImmersionFPT.Main
