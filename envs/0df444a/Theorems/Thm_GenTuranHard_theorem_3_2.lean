-- Prove2me | Theorems.Thm_GenTuranHard_theorem_3_2
-- name    : GenTuranHard.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:44.944264+00:00
-- url     : https://prove2.me/theorems/fd35f63c-0f0e-40b9-827a-0fed3c3c4455
-- title:
--   Theorem 3.2 — estimates $L + Sz - a \le \mathrm{ex}' \le \mathrm{ex} \le L + Sz + b$ transfer additive hardness
-- statement:
--   Let $T$ be a fixed graph with $e(T) > 0$, $\mathcal F$ a nonempty family of graphs, and $\varepsilon > 0$. Let $\mathcal G$ be a class of input graphs, and suppose that the graph parameter $z = z(G)$ is NP-hard to approximate within an additive error of $g(n)$ for $G \in \mathcal G$, $n = v(G)$. Suppose that for every $G \in \mathcal G$ one can construct in polynomial time a graph $Z = Z(G)$ with
--
--   $$
--   L + Sz - a \le \mathrm{ex}'(Z, T, \mathcal F) \le \mathrm{ex}(Z, T, \mathcal F) \le L + Sz + b,
--   $$
--
--   where $L = L(G) \ge 0$ and $S = S(G) > 0$ are polynomial-time computable rational numbers and $a, b \ge 0$. If
--
--   $$
--   a + b + v(Z)^{v(T) - \varepsilon} \le g(n)\, S,
--   $$
--
--   then approximating $\mathrm{ex}(Z, T, \mathcal F)$, and approximating $\mathrm{ex}'(Z, T, \mathcal F)$, within an additive error of $v(Z)^{v(T)-\varepsilon}$ is NP-hard for $Z \in \{Z(G) : G \in \mathcal G\}$.
--
--   This is the reduction step that turns the two-sided estimate (2.1) into hardness.
--
--   **Formalization Note** "Constructed in polynomial time" and "polynomial-time computable rational" mean that polynomial-time maps send the code of $G$ to the code of $Z(G)$, of $L(G)$ and of $S(G)$. The middle inequality $\mathrm{ex}' \le \mathrm{ex}$ holds for every graph, so only the outer two inequalities are hypotheses. The conclusion states both parameters, as in the proof ("or" in the statement).
--
--   Differences from the source:
--   - reading: “NP-hard” (unspecified reduction notion) → AddApproxNPHard: for every NP language a polynomial-time instance map and a polynomial-time answer map that uses one approximate value, correct for every admissible rational answer; reason: the reductions of Theorem 3.2 and Corollary 3.3 have this one-query form; it implies hardness under polynomial-time oracle (Cook) reductions
--   - encoding: input graphs and rational numbers (format unspecified) → encGraph (n in unary, then the n² adjacency bits) and encRat (sign, |numerator|, denominator in a self-delimiting binary code); reason: explicit injective codes; polynomial time in the code length of encGraph is polynomial time in n
--   - encoding: ex and ex′ as maxima over (spanning) 𝓕-free subgraphs H ⊆ G → Finset.sup over G.Subgraph (with H.verts = univ for ex′); reason: a finite maximum in ℕ; the empty subgraph is 𝓕-free whenever no member of 𝓕 is empty
--   - encoding: the chain L + Sz − a ≤ ex′ ≤ ex ≤ L + Sz + b → the two hypotheses L + Sz − a ≤ ex′ and ex ≤ L + Sz + b; reason: ex′ ≤ ex holds for every graph (every spanning subgraph is a subgraph), so the middle link is not an assumption
--   - reading: “NP-hard to approximate ex(Z, T, F) or ex′(Z, T, F)” → both: hardness for ex and hardness for ex′; reason: the proof treats ex and says the proof for ex′ is the same; the conjunction is the stronger reading
--   - encoding: n^{v(T)−ε} → (n : ℝ) ^ ((v(T) : ℝ) − ε) (Real.rpow); reason: the real power; for n ≥ 1 it is the usual power
--   - generalization: every graph of a family has at least one edge (footnote 1, p.2, a standing assumption of the paper) → 𝓕 any nonempty set of finite graphs; edgeless members are allowed; reason: the proof (p.11) uses nothing about the members of 𝓕; when every member has an edge the Lean statement is the source's
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Theorem 3.2, pp.10–11

import Mathlib
import Definitions.Def_GenTuranHard_exT
import Definitions.Def_GenTuranHard_AddApproxNPHard

set_option autoImplicit false

namespace GenTuranHard

/-- **Theorem 3.2** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, Theorem 3.2,
pp.10–11): estimates give hardness. Let `T` be a fixed graph with `e(T) > 0`, `𝓕` a nonempty family and
`ε > 0`. Let `𝒢` (`Dom`) be a class of input graphs on which the parameter `z` is NP-hard to approximate
within the additive error `g(n)`. Suppose that for every `G ∈ 𝒢` a graph `Z = Z(G)` is constructed in
polynomial time with `L + Sz − a ≤ ex′(Z, T, 𝓕)` and `ex(Z, T, 𝓕) ≤ L + Sz + b`, where `L = L(G) ≥ 0`
and `S = S(G) > 0` are polynomial-time computable rationals and `a, b ≥ 0`. If
`a + b + v(Z)^{v(T)−ε} ≤ g(n)S`, then approximating `ex(Z, T, 𝓕)`, and approximating `ex′(Z, T, 𝓕)`,
within the additive error `v(Z)^{v(T)−ε}` is NP-hard for `Z ∈ {Z(G) : G ∈ 𝒢}`.

**Formalization Note** "Constructed in polynomial time" and "polynomial-time computable rational" are
`CookPvsNP.PolyTimeComputable` maps on the codes `encGraph` and `encRat`. The middle inequality
`ex′ ≤ ex` of the source's chain holds for every graph and is not a hypothesis. "ex or ex′" in the
conclusion is read as each of the two, as in the proof. -/
theorem theorem_3_2 {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W)
    (hTe : T.edgeSet.Nonempty) (Fam : Set FinGraph) (hFne : Fam.Nonempty) (ε : ℝ) (hε : 0 < ε)
    (Dom : FinGraph → Prop) (z : FinGraph → ℝ) (g : ℕ → ℝ)
    (hz : AddApproxNPHard encGraph Dom z (fun G => g G.1))
    (Zc : FinGraph → FinGraph)
    (hZc : ∃ h : List Bool → List Bool, CookPvsNP.PolyTimeComputable h ∧
      ∀ G, Dom G → h (encGraph G) = encGraph (Zc G))
    (L S : FinGraph → ℚ)
    (hL : ∃ h : List Bool → List Bool, CookPvsNP.PolyTimeComputable h ∧
      ∀ G, Dom G → h (encGraph G) = encRat (L G))
    (hS : ∃ h : List Bool → List Bool, CookPvsNP.PolyTimeComputable h ∧
      ∀ G, Dom G → h (encGraph G) = encRat (S G))
    (hL0 : ∀ G, Dom G → 0 ≤ L G) (hS0 : ∀ G, Dom G → 0 < S G)
    (a b : FinGraph → ℝ) (ha : ∀ G, Dom G → 0 ≤ a G) (hb : ∀ G, Dom G → 0 ≤ b G)
    (hlow : ∀ G, Dom G → (L G : ℝ) + (S G : ℝ) * z G - a G ≤ (exSpan (Zc G).2 T Fam : ℝ))
    (hup : ∀ G, Dom G → (exT (Zc G).2 T Fam : ℝ) ≤ (L G : ℝ) + (S G : ℝ) * z G + b G)
    (herr : ∀ G, Dom G →
      a G + b G + ((Zc G).1 : ℝ) ^ ((Fintype.card W : ℝ) - ε) ≤ g G.1 * (S G : ℝ)) :
    AddApproxNPHard encGraph (fun Z => ∃ G, Dom G ∧ Z = Zc G) (fun Z => (exT Z.2 T Fam : ℝ))
        (fun Z => (Z.1 : ℝ) ^ ((Fintype.card W : ℝ) - ε)) ∧
      AddApproxNPHard encGraph (fun Z => ∃ G, Dom G ∧ Z = Zc G) (fun Z => (exSpan Z.2 T Fam : ℝ))
        (fun Z => (Z.1 : ℝ) ^ ((Fintype.card W : ℝ) - ε)) := by sorry

end GenTuranHard
