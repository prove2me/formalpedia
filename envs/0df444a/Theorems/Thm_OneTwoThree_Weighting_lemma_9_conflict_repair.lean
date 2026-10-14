-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_9_conflict_repair
-- name    : OneTwoThree.Weighting.lemma_9_conflict_repair
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-11T12:21:57.810511+00:00
-- url     : https://prove2.me/theorems/d46cc3c9-8a1b-4882-b763-4c8b4dac5270
-- title:
--   Lemma 9 conflict repair — elementary ±1 path-shift resolving the v₀–u₀ conflict
-- statement:
--   The elementary ±1 path-shift repair from the proof of Lemma 9 (Keusch, *A Solution
--   to the 1-2-3 Conjecture*, arXiv:2303.02611v4, p. 10).
--
--   The paper combines three weightings into one weighting $\omega$ of $G$: $\omega_1$
--   on $E(B)$ (Lemma 3), $\omega_2$ on the $v_0$-incident edges, and $\omega_3$ on
--   $E(R,B)$ from the Lemma 5 path version (`OneTwoThree.Weighting.lemma_5_path_refinement`,
--   `d6776149-ae19-44e2-95f8-b7665a7474ce`). Under $\omega$ every coloring conflict is
--   already resolved except possibly between $v_0$ and its unique red neighbour $u_0$:
--   vertices of $R$ have even weighted degree, vertices of $B$ carry odd values forming
--   a proper coloring on $B$-$B$ edges. When $s_\omega(v_0) = s_\omega(u_0)$ (both even),
--   the paper repairs the conflict by shifting edge weights by $\pm 1$ along the
--   blue-to-blue path $q$ in $G(R,B)$ avoiding $u_0$ (the `hpath` hypothesis of Lemma 9,
--   `5808bb45-2962-4f1b-a71f-ef4052d1eb23`):
--
--   - the three $\beta$-cases ($\beta(v_1),\beta(v_k)\in\{1,3\}$) all produce one
--     common shift direction $\varepsilon\in\{+1,-1\}$: the two $v_0$-edges shift by
--     $\varepsilon$ and the two endpoint path edges shift by $-\varepsilon$, staying in
--     $\{1,2,3\}$. Lemma 5 (iv)/(vi) are exactly what makes this legal: the endpoint
--     path edge avoids $1$ (resp. $3$) according to the $\alpha$-case. This node takes
--     that common consequence as four shift-validity hypotheses;
--   - at each interior blue path vertex, Lemma 5 (v) keeps the two incident path-edge
--     weights summing to $3$, $4$ or $5$, so both can shift by $\pm 1$ oppositely with
--     the weighted degree unchanged; interior red vertices keep even weighted degree,
--     and $u_0$ lies off the path so $s(u_0)$ is untouched.
--
--   The net effect is $s_{\omega'}(v_0) = s_\omega(v_0) + 2\varepsilon \ne
--   s_{\omega'}(u_0)$ while every other weighted degree keeps its parity class, so
--   $\omega'$ is a vertex-coloring $\{1,2,3\}$-weighting of $G$. No flow machinery is
--   used (the s-t network belongs to Lemma 4); the T-join-reassignment reframe of the
--   lemma_5 retriage applies. Once the cited engine children are proved, a PROVE worker
--   assembles $\omega$ and discharges this node.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 10, proof of Lemma 9 (conflict-repair step)

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

/-- Lemma 9 conflict repair (Keusch, arXiv:2303.02611v4, p. 10, proof of Lemma 9).

The paper combines weightings `ω₁` (on `E(B)`), `ω₂` (on `v₀`-incident edges) and `ω₃`
(on `E(R,B)`, from the Lemma 5 path version) into one weighting `ω` of `G` under which
the only possible coloring conflict is between `v₀` and its unique red neighbour `u₀`
(`R` is even-weighted, `B` carries odd proper-coloring values). When
`s_ω(v₀) = s_ω(u₀)`, the paper repairs the conflict by shifting edge weights by `±1`
along the `B`-to-`B` path `q` in `G(R,B)` avoiding `u₀`:

- the three `β`-cases all yield one common shift direction `ε ∈ {+1,-1}`: the two
  `v₀`-edges shift by `ε`, the two path edges at the endpoints shift by `-ε`, all
  staying in `{1,2,3}` (this is what Lemma 5 (iv)/(vi) buy: the endpoint path edges
  avoid `1` resp. `3` according to the `α`-case);
- at every interior `B` path vertex Lemma 5 (v) keeps the two incident path-edge
  weights summing to `3`, `4` or `5`, so both can shift by `±1` oppositely with the
  weighted degree fixed; interior `R` vertices keep even weighted degree, and `u₀`
  is off the path so `s(u₀)` is untouched.

Hence `s_ω'(v₀) = s_ω(v₀) + 2ε ≠ s_ω'(u₀)` while every other weighted degree keeps
its parity class: `ω'` is vertex-coloring. This node is that elementary repair step
as an interface: the engine output `ω` with its invariants, the path data `q`
(`hpath` of Lemma 9), the endpoint shift validity (the three `β`-cases' common
consequence), and Lemma 5 (v) along `q`. -/
theorem lemma_9_conflict_repair {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v₀ : V) (R B : Finset V)
    (hRindep : G.IsIndepSet (R : Set V))
    (u₀ : V) (hu₀ : u₀ ∈ R) (hN : G.neighborFinset v₀ ∩ R = {u₀})
    (ω : Sym2 V → ℕ) (hω : IsWeighting G 3 ω)
    (hReven : ∀ v ∈ R, Even (wdeg G ω v))
    (hBodd : ∀ v ∈ B, Odd (wdeg G ω v))
    (hBcol : ∀ u v, u ∈ B → v ∈ B → G.Adj u v → wdeg G ω u ≠ wdeg G ω v)
    (hconf : wdeg G ω v₀ = wdeg G ω u₀)
    {a b : V} (ha : a ∈ G.neighborFinset v₀ ∩ B) (hb : b ∈ G.neighborFinset v₀ ∩ B)
    (q : (G.between (R : Set V) (B : Set V)).Walk a b)
    (hqpath : q.IsPath) (hqlen : 0 < q.length) (hqsup : u₀ ∉ q.support)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hshift_a : (ω (s(v₀, a)) : ℤ) + ε ∈ ({1, 2, 3} : Finset ℤ))
    (hshift_b : (ω (s(v₀, b)) : ℤ) + ε ∈ ({1, 2, 3} : Finset ℤ))
    (hcomp_a : (ω (s(a, q.getVert 1)) : ℤ) - ε ∈ ({1, 2, 3} : Finset ℤ))
    (hcomp_b : (ω (s(q.getVert (q.length - 1), b)) : ℤ) - ε ∈ ({1, 2, 3} : Finset ℤ))
    (hv : ∀ j, 0 < j → j < q.length → q.getVert j ∈ B →
      ω (s(q.getVert (j - 1), q.getVert j)) +
        ω (s(q.getVert j, q.getVert (j + 1))) ∈ ({3, 4, 5} : Finset ℕ)) :
    ∃ ω' : Sym2 V → ℕ, IsWeighting G 3 ω' ∧ IsVertexColoring G ω' := by sorry

end OneTwoThree.Weighting
