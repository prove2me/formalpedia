-- Prove2me | Theorems.Thm_FullImmersionFPT_Main_proposition_56
-- name    : FullImmersionFPT.Main.proposition_56
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:49:36.161816+00:00
-- url     : https://prove2.me/theorems/49949ec9-ad77-44df-963a-e986a5434e91
-- title:
--   Proposition 56 — rooted full immersion testing between colorless decorated graphs in O(n⁵) time
-- statement:
--   Let $\mathcal G,\mathcal H$ be colorless decorated graphs labeled over the same $\mathbb F_2^U$, with $|V(\mathcal H)|=\delta_0$. Then one can verify whether $\mathcal H$ is fully immersed by $\mathcal G$ (§13.2: after shiftings, an injective root-respecting vertex map and edge-disjoint trails covering $E(G)$ with the right weights; root values must agree) in time
--   $$O_{\delta_0,|U|}(n^5),\qquad n=|V(\mathcal G)|.$$
--   Formally: one program $P$ (input: the codes of $\mathcal G$ and $\mathcal H$) and for all $\delta_0,|U|$ a constant $c$ with $P$ deciding the question within $c\,n^5+c$ steps. Labeled tour graphs are colorless decorated graphs without roots, so this is the rooted form of Theorem 1.
--
--   Differences from the source:
--   - reading: "we can find/compute/test … in time O_{δ0,|U|}(n⁵)" → one program P of the published TrulySubcubicAPSP word RAM and a word-size factor b, fixed before every input, uniform in δ0 and |U| (H is part of the input), with c chosen after δ0 and |U|; on every input and every word size W ≥ b(⌊log₂(N+2)⌋+1) (FOMCMonDep.WordSizeOK, N = input length plus largest absolute entry) P halts within the explicit bound with a correct output; reason: the paper fixes a RAM storing graphs as adjacency lists of half-edges with constant-time access (p. 15) but names no formal machine; unit-cost word RAM with logarithmic words is the reading; each O(·) is an explicit constant chosen after the parameters it is subscripted with
--   - encoding: colorless decorated graphs G, H (Part III: one fixed F₂^U) → two DecoCode inputs with q = 0 colors and the same label dimension d; reason: Part III fixes the label space for all graphs; colorless means every color set is empty
--   - encoding: "verify if H is fully immersed by G" → FOMCMonDep.DecidesWithin: accept iff G fully immerses H; reason: a decision problem
--   - encoding: decorated graphs (G, λ, R, ρ, α) over F₂^U with q colors → Decorated V H d q with labels Fin d → ZMod 2 (d = |U|), root : V → Option ℕ, colors Finset (Fin q); inputs as DecoCode edge lists; reason: Lean convention; every decorated graph is isomorphic to a code
--   - encoding: graphs with loops and parallel edges, edges {h₁, h₂} of half-edges (§5) → Multigraph V H: finite vertex and half-edge sets in ambient types, inc, mate; an edge is s(h, mate h) : Sym2 H; a trail is the list of the tail half-edges of its arcs; reason: the paper's half-edge model; keeping the ambient types fixed lets splitting off delete vertices and half-edges
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 67, Proposition 56

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_Decorated

set_option autoImplicit false

open Classical

namespace FullImmersionFPT.Main

/-- **Proposition 56** (p. 67). One program `P` decides, for colorless decorated graphs `G` (`n`
vertices) and `H` with `|V(H)| = δ₀` (labels in the same `F₂^U`), whether `H` is fully immersed by
`G`, within `c · n⁵ + c` steps, `c` depending only on `δ₀` and `|U|`. -/
theorem proposition_56 :
    ∃ (P : List TrulySubcubicAPSP.Instr) (b : ℕ), ∀ δ₀ d : ℕ, ∃ c : ℕ,
      ∀ (n m n' m' : ℕ) (K : DecoCode n m d 0) (L : DecoCode n' m' d 0),
        K.toDeco.IsDecorated → L.toDeco.IsDecorated → n' = δ₀ → ∀ W : ℕ,
        FOMCMonDep.WordSizeOK b (K.words ++ L.words) W →
        FOMCMonDep.DecidesWithin P W (c * n ^ 5 + c) (K.words ++ L.words)
          (K.toDeco.FullyImmerses L.toDeco) := by sorry

end FullImmersionFPT.Main
