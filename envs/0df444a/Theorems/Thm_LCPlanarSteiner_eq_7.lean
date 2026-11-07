-- Prove2me | Theorems.Thm_LCPlanarSteiner_eq_7
-- name    : LCPlanarSteiner.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:09:18.622352+00:00
-- url     : https://prove2.me/theorems/8cf96394-fcf7-4184-afe8-1cb1f0513581
-- title:
--   Display (7) — additive repair: $\ell(P_t) \le b_t + \sigma B/2 \le b_t + E$ and $c(F) \le 416D^3X/\sigma$
-- statement:
--   Let $G$, $r$, the terminals, $D$, the purchases $x$ of cost $X$ and the dominated distributions be as in Lemma 3.8, now with endpoint-specific bounds $0 \le b_t \le B$, $B > 0$, and let $E > 0$ be an additive error. Put $\sigma = \min\{1, 2E/B\}$.
--
--   **Display (7).** A deterministic algorithm, running in time polynomial in the binary description and the inverse accuracy $1/\sigma$, returns for each terminal $t$ a simple path $P_t$ from $r$ to $t$ such that the union $F$ of their arcs satisfies
--   $$
--   \ell(P_t) \le b_t + \frac{\sigma B}{2} \le b_t + E,\qquad c(F) \le \frac{416 D^3 X}{\sigma} . \tag{7}
--   $$
--   Root-equal terminals receive empty paths.
--
--   This is the endpoint-specific additive repair that Lemma 4.6 applies to the median arms of the density LP, in $G$ and in its reverse.
--
--   **Formalization Note** The paper obtains (7) from Lemma 3.8 with $H = (1 + \sigma/2)B$ and $\delta = \sigma B/(2D)$; the statement is about the output, not the parameter choice.
--
--   Differences from the source:
--   - reading: both choices have the claimed polynomial time in the binary supplied description and inverse accuracy → one function computed by a Turing machine in time polynomial in the length of the binary encoding padded by ⌈1/σ⌉ symbols; reason: the paper names no machine model; the padding makes the input length the binary size plus the inverse accuracy up to one
--   - generalization: the same algorithm gives paths P_t and a union F → one simple path per terminal; F is the union of their arcs; reason: any union containing the paths costs at least as much; root-equal terminals get the empty path, the only simple path from the root to itself
--   - encoding: polynomially supported unit distributions, a terminal set, planar G → finite lists of (simple path, weight) per terminal, a list of distinct terminals, planarity of the underlying graph of the input; reason: Lean convention; G is planar throughout the paper (p.2)
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §3.4 (The two parameter choices), display (7), p.9

import Mathlib
import Definitions.Def_LCPlanarSteiner_RootData
import Definitions.Def_LCPlanarSteiner_pcost
import Definitions.Def_LCPlanarSteiner_underlying
import Definitions.Def_LCPlanarSteiner_encRepairIn
import Definitions.Def_LCPlanarSteiner_encPaths
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace LCPlanarSteiner

/-- **Display (7): endpoint-specific additive repair.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §3.4 ("The two parameter choices"), p.9: "For endpoint-specific bounds b_t ≤ B, B > 0, and
additive error E > 0, put σ = min{1, 2E/B}, H = (1 + σ/2)B, and δ = σB/(2D). The same algorithm
gives ℓ(P_t) ≤ b_t + σB/2 ≤ b_t + E, c(F) ≤ 416D³X/σ. (7) Both choices have the claimed polynomial
time in the binary supplied description and inverse accuracy. Root-equal endpoints use empty paths."

There is a function `alg`, computable by a Turing machine in time polynomial in the length of
`encRepairIn (R, B, E)` (the binary datum padded by `⌈1/σ⌉` symbols), such that for every valid rooted
datum `R` in a planar graph with bounds `0 ≤ b_t ≤ B`, `B > 0` and `E > 0`, with
`σ = min{1, 2E/B}`: `alg` returns one path per terminal; the path `P_t` is a simple path from the root
to `t` with `ℓ(P_t) ≤ b_t + σB/2`, and `σB/2 ≤ E`; and the union `F` of the returned arcs costs
`c(F) ≤ 416 D³ X / σ`.

**Formalization Note.** A root-equal terminal gets the empty path (the only simple path from the
root to itself). "Inverse accuracy" in the time bound is the padding `⌈1/σ⌉`. -/
theorem eq_7 :
    ∃ alg : RootData × ℚ × ℚ → List (List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encRepairIn encPaths alg) ∧
      ∀ (R : RootData) (B E : ℚ), R.Valid B → 0 < B → 0 < E →
        RobertsonSeymour1986.GM5.IsPlanar (underlying R.net R.net.allArcs) →
        (alg (R, B, E)).length = R.terms.length ∧
        (∀ i < R.terms.length,
          IsSPath R.net R.root (R.terms.getD i (0, 0, [])).1 ((alg (R, B, E)).getD i []) ∧
          plen R.net ((alg (R, B, E)).getD i []) ≤
            (R.terms.getD i (0, 0, [])).2.1 + min 1 (2 * E / B) * B / 2) ∧
        min 1 (2 * E / B) * B / 2 ≤ E ∧
        pcost R.net (alg (R, B, E)).flatten.toFinset ≤
          416 * (R.D : ℚ) ^ 3 * R.X / min 1 (2 * E / B) := by sorry

end LCPlanarSteiner
