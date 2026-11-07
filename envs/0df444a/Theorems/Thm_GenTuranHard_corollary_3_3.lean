-- Prove2me | Theorems.Thm_GenTuranHard_corollary_3_3
-- name    : GenTuranHard.corollary_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:01.029749+00:00
-- url     : https://prove2.me/theorems/05c5a470-21b1-4ab2-ac95-8c5a0a75c415
-- title:
--   Corollary 3.3 — rounding: if $a + b + v(Z)^{v(T)-\varepsilon} < S/2$, hardness of computing $\mathrm{cut}_{k-1}$ transfers
-- statement:
--   Let $T$ be a fixed graph with $e(T) > 0$, $\mathcal F$ a nonempty family of graphs with $k = \min_{F \in \mathcal F} \chi(F) \ge 3$, and $\varepsilon > 0$. Let $\mathcal G$ be a class of input graphs on which computing $z = \mathrm{cut}_{k-1}(G)$ is NP-hard. Suppose that for every $G \in \mathcal G$ one can construct in polynomial time a graph $Z = Z(G)$ with
--
--   $$
--   L + Sz - a \le \mathrm{ex}'(Z, T, \mathcal F) \le \mathrm{ex}(Z, T, \mathcal F) \le L + Sz + b,
--   $$
--
--   where $L = L(G) \ge 0$ and $S = S(G) > 0$ are polynomial-time computable rational numbers and $a, b \ge 0$. If
--
--   $$
--   a + b + v(Z)^{v(T) - \varepsilon} < \frac{S}{2},
--   $$
--
--   then approximating $\mathrm{ex}(Z, T, \mathcal F)$, and approximating $\mathrm{ex}'(Z, T, \mathcal F)$, within an additive error of $v(Z)^{v(T)-\varepsilon}$ is NP-hard for $Z \in \{Z(G) : G \in \mathcal G\}$.
--
--   Since $z$ is an integer, an approximation within error less than $1/2$ determines it; this is the form in which Theorem 1.5 is derived.
--
--   **Formalization Note** "Computing $z$ is NP-hard" is NP-hardness of approximation within error $0$. The middle inequality $\mathrm{ex}' \le \mathrm{ex}$ holds for every graph and is not a hypothesis.
--
--   Differences from the source:
--   - reading: “NP-hard” (unspecified reduction notion) → AddApproxNPHard: for every NP language a polynomial-time instance map and a polynomial-time answer map that uses one approximate value, correct for every admissible rational answer; reason: the reductions of Theorem 3.2 and Corollary 3.3 have this one-query form; it implies hardness under polynomial-time oracle (Cook) reductions
--   - encoding: input graphs and rational numbers (format unspecified) → encGraph (n in unary, then the n² adjacency bits) and encRat (sign, |numerator|, denominator in a self-delimiting binary code); reason: explicit injective codes; polynomial time in the code length of encGraph is polynomial time in n
--   - encoding: ex and ex′ as maxima over (spanning) 𝓕-free subgraphs H ⊆ G → Finset.sup over G.Subgraph (with H.verts = univ for ex′); reason: a finite maximum in ℕ; the empty subgraph is 𝓕-free whenever no member of 𝓕 is empty
--   - encoding: k = min_{F∈𝓕} χ(F) → hypotheses: no member of 𝓕 is (k−1)-colorable, and some member is k-colorable; reason: these two conditions say exactly that the least chromatic number in 𝓕 is k (χ(F) ≤ r iff F is r-colorable)
--   - encoding: the chain L + Sz − a ≤ ex′ ≤ ex ≤ L + Sz + b → the two hypotheses L + Sz − a ≤ ex′ and ex ≤ L + Sz + b; reason: ex′ ≤ ex holds for every graph, so the middle link is not an assumption
--   - reading: “NP-hard to approximate ex(Z, T, F) or ex′(Z, T, F)” → both: hardness for ex and hardness for ex′; reason: as in Theorem 3.2; the conjunction is the stronger reading
--   - encoding: n^{v(T)−ε} → (n : ℝ) ^ ((v(T) : ℝ) − ε) (Real.rpow); reason: the real power; for n ≥ 1 it is the usual power
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Corollary 3.3, p.11

import Mathlib
import Definitions.Def_GenTuranHard_exT
import Definitions.Def_GenTuranHard_cutR
import Definitions.Def_GenTuranHard_AddApproxNPHard

set_option autoImplicit false

namespace GenTuranHard

/-- **Corollary 3.3** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, Corollary 3.3, p.11):
rounding an integer parameter. Let `T` be a fixed graph with `e(T) > 0`, `𝓕` a nonempty family with
`k = min_{F ∈ 𝓕} χ(F) ≥ 3`, and `ε > 0`. Let `𝒢` (`Dom`) be a class of input graphs on which computing
`z = cut_{k−1}(G)` is NP-hard. Suppose that for every `G ∈ 𝒢` a graph `Z = Z(G)` is constructed in
polynomial time with `L + Sz − a ≤ ex′(Z, T, 𝓕)` and `ex(Z, T, 𝓕) ≤ L + Sz + b`, where `L ≥ 0`,
`S > 0` are polynomial-time computable rationals and `a, b ≥ 0`. If `a + b + v(Z)^{v(T)−ε} < S/2`, then
approximating `ex(Z, T, 𝓕)`, and approximating `ex′(Z, T, 𝓕)`, within the additive error
`v(Z)^{v(T)−ε}` is NP-hard for `Z ∈ {Z(G) : G ∈ 𝒢}`.

**Formalization Note** `k = min χ(F)` is encoded by `hkF` (no member is `(k−1)`-colorable) and `hkF'`
(some member is `k`-colorable). "Computing `z` is NP-hard" is `AddApproxNPHard` with error `0`. The
middle inequality `ex′ ≤ ex` holds for every graph and is not a hypothesis; "ex or ex′" is read as each
of the two. -/
theorem corollary_3_3 {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W)
    (hTe : T.edgeSet.Nonempty) (Fam : Set FinGraph) (hFne : Fam.Nonempty)
    (k : ℕ) (hk3 : 3 ≤ k) (hkF : ∀ F ∈ Fam, ¬ F.2.Colorable (k - 1))
    (hkF' : ∃ F ∈ Fam, F.2.Colorable k) (ε : ℝ) (hε : 0 < ε)
    (Dom : FinGraph → Prop)
    (hz : AddApproxNPHard encGraph Dom (fun G => (cutR (k - 1) G.2 : ℝ)) (fun _ => 0))
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
    (hlow : ∀ G, Dom G →
      (L G : ℝ) + (S G : ℝ) * (cutR (k - 1) G.2 : ℝ) - a G ≤ (exSpan (Zc G).2 T Fam : ℝ))
    (hup : ∀ G, Dom G →
      (exT (Zc G).2 T Fam : ℝ) ≤ (L G : ℝ) + (S G : ℝ) * (cutR (k - 1) G.2 : ℝ) + b G)
    (herr : ∀ G, Dom G →
      a G + b G + ((Zc G).1 : ℝ) ^ ((Fintype.card W : ℝ) - ε) < (S G : ℝ) / 2) :
    AddApproxNPHard encGraph (fun Z => ∃ G, Dom G ∧ Z = Zc G) (fun Z => (exT Z.2 T Fam : ℝ))
        (fun Z => (Z.1 : ℝ) ^ ((Fintype.card W : ℝ) - ε)) ∧
      AddApproxNPHard encGraph (fun Z => ∃ G, Dom G ∧ Z = Zc G) (fun Z => (exSpan Z.2 T Fam : ℝ))
        (fun Z => (Z.1 : ℝ) ^ ((Fintype.card W : ℝ) - ε)) := by sorry

end GenTuranHard
