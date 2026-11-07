-- Prove2me | Theorems.Thm_LCPlanarSteiner_lemma_3_8
-- name    : LCPlanarSteiner.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:09:05.740609+00:00
-- url     : https://prove2.me/theorems/1a156365-5f4c-44fd-978a-178456ca404b
-- title:
--   Lemma 3.8 — full-witness rounding: $\ell(P_t) \le b_t + D\delta$ and $c(F) \le 32D^2(1+\beta)X$
-- statement:
--   Let $G$ be a planar graph with nonnegative costs and lengths, $r$ a root, and $T$ a set of distinct terminals, $k$ of them other than $r$, $D = 1 + \lceil \log_2 k \rceil$. Let purchases $x \ge 0$ of cost $X = \sum_e c_e x_e$ dominate finitely supported unit distributions of simple $r$–$t$ paths, the paths of terminal $t$ having length at most $b_t$, where $0 \le b_t \le H$ and $H > 0$. Let $\delta > 0$, $M = H + D\delta$ and
--   $$
--   \beta = 1 + \Bigl\lceil \frac{M + 2H}{\delta} \Bigr\rceil . \tag{2}
--   $$
--
--   **Lemma 3.8 (Full-witness rounding).** A deterministic algorithm, running in time polynomial in the binary description and $1 + H/\delta$, returns for each terminal $t$ a simple path $P_t$ from $r$ to $t$ such that the union $F$ of their arcs satisfies
--   $$
--   \ell(P_t) \le b_t + D\delta,\qquad c(F) \le 32 D^2 (1 + \beta) X . \tag{5}
--   $$
--
--   The rounding keeps each terminal's full fractional witness and its bound $b_t$; the forest algorithm uses it through display (7).
--
--   Differences from the source:
--   - reading: a deterministic algorithm whose time is polynomial in the binary supplied description and 1 + H/δ → one function computed by a Turing machine in time polynomial in the length of the binary encoding padded by ⌈H/δ⌉ symbols; reason: the paper names no machine model; the padding makes the input length the binary size plus H/δ up to one
--   - generalization: returns a shared original union and paths → returns one simple path per terminal; F is the union of their arcs; reason: any union containing the paths costs at least as much, and the proof's paths are shortest paths in the union (simple)
--   - encoding: polynomially supported unit distributions, a terminal set T, planar G → finite lists of (simple path, weight) per terminal, a list of distinct terminals, planarity of the underlying graph of the input; reason: Lean convention; G is planar throughout the paper (p.2)
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.8, pp.8–9; display (2), p.6

import Mathlib
import Definitions.Def_LCPlanarSteiner_RootData
import Definitions.Def_LCPlanarSteiner_pcost
import Definitions.Def_LCPlanarSteiner_underlying
import Definitions.Def_LCPlanarSteiner_encRoundIn
import Definitions.Def_LCPlanarSteiner_encPaths
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace LCPlanarSteiner

/-- **Lemma 3.8 (Full-witness rounding).**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.8, pp.8–9: "Suppose purchases x of cost X dominate polynomially supported unit
distributions of original simple paths, with paths to t of length at most b_t, where 0 ≤ b_t ≤ H and
H > 0. For δ > 0, put M = H + Dδ and define β by (2). A deterministic algorithm returns a shared
original union and paths satisfying ℓ(P_t) ≤ b_t + Dδ, c(F) ≤ 32D²(1 + β)X. (5) Its time is
polynomial in the binary supplied description and 1 + H/δ." Display (2), p.6:
"β = 1 + ⌈(M + 2H)/δ⌉."

There is a function `alg`, computable by a Turing machine in time polynomial in the length of
`encRoundIn (R, H, δ)` (the binary datum padded by `⌈H/δ⌉` symbols), such that for every valid rooted
datum `R` in a planar graph with bounds `0 ≤ b_t ≤ H`, `H > 0` and `δ > 0`, with `M = H + Dδ` and
`β = 1 + ⌈(M + 2H)/δ⌉`: `alg` returns one path per terminal, the path `P_t` of terminal `t` is a
simple path of `G` from the root to `t` with `ℓ(P_t) ≤ b_t + Dδ`, and the union `F` of the arcs of
the returned paths costs `c(F) ≤ 32 D² (1 + β) X`.

**Formalization Note.** The returned union is represented by the paths it contains; any union
containing them costs at least as much. Planarity is of the underlying graph of the whole input.
"`1 + H/δ`" in the time bound is the padding `⌈H/δ⌉`. -/
theorem lemma_3_8 :
    ∃ alg : RootData × ℚ × ℚ → List (List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encRoundIn encPaths alg) ∧
      ∀ (R : RootData) (H δ : ℚ), R.Valid H → 0 < H → 0 < δ →
        RobertsonSeymour1986.GM5.IsPlanar (underlying R.net R.net.allArcs) →
        (alg (R, H, δ)).length = R.terms.length ∧
        (∀ i < R.terms.length,
          IsSPath R.net R.root (R.terms.getD i (0, 0, [])).1 ((alg (R, H, δ)).getD i []) ∧
          plen R.net ((alg (R, H, δ)).getD i []) ≤ (R.terms.getD i (0, 0, [])).2.1 + R.D * δ) ∧
        pcost R.net (alg (R, H, δ)).flatten.toFinset ≤
          32 * (R.D : ℚ) ^ 2 * (1 + (1 + ⌈(H + R.D * δ + 2 * H) / δ⌉₊ : ℕ)) * R.X := by sorry

end LCPlanarSteiner
