-- Prove2me | Theorems.Thm_LCPlanarSteiner_lemma_4_3
-- name    : LCPlanarSteiner.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:48.841919+00:00
-- url     : https://prove2.me/theorems/6cca2ddc-b2c1-4e88-8096-4001b0e15695
-- title:
--   Lemma 4.3 — planar extraction: density $\le 27D_rc(F^\star)/r$, and junctions (13) of density $\le 297D_r^2c(F^\star)/(\eta r)$
-- statement:
--   Let $G$ be a graph with nonnegative costs and lengths, $h > 0$, and $F^\star$ a set of arcs with planar underlying graph that serves $r \ge 1$ pairs $(s_i, t_i)$: $\mathrm{dist}_{F^\star}(s_i, t_i) \le h$ for all $i$.
--
--   **Lemma 4.3 (Planar extraction).**
--   1. There are an original subgraph $G^\star$, a directed simple path $P \subseteq G^\star$ of length at most $h$, and a nonempty pair set $J$ with strict original witnesses $W_i \subseteq G^\star$ ($i \in J$) meeting $P$, such that
--   $$
--   \frac{c(G^\star)}{|J|} \le C_E D_r \frac{c(F^\star)}{r},\qquad C_E = 27 .
--   $$
--   2. Consequently, for $0 < \eta \le 1$, some original junction $(H', v, I)$ satisfies (8), i.e. $\mathrm{dist}_{H'}(s_i, v) + \mathrm{dist}_{H'}(v, t_i) \le (1+\eta)h$ for $i \in I$, and
--   $$
--   \frac{c(H')}{|I|} \le \frac{C_{NE} D_r^2}{\eta r}\, c(F^\star),\qquad C_{NE} = 11 C_E = 297 . \tag{13}
--   $$
--
--   At an optimal strict forest the right-hand side of (13) is the paper's $C_{NE} D_r^2 \mathrm{OPT}^F_h/(\eta r)$.
--
--   **Formalization Note** Divisions are cleared. Self-pairs are allowed. $h > 0$ is the standing assumption of §§3–4 (p.5).
--
--   Differences from the source:
--   - generalization: (13): c(H′)/|I| ≤ C_NE D_r²/(ηr) · OPT^F_h → c(H′)/|I| ≤ 297 D_r² c(F⋆)/(ηr) for the given strict planar forest F⋆; reason: G is planar in the paper (p.2), so an optimal strict forest is a strict planar forest and taking it as F⋆ gives the printed bound; the proof ("apply lemma 4.1 and average over its partition") works for every strict planar F⋆
--   - encoding: C_E = 27, C_NE = 11C_E; densities as quotients; witnesses meeting P → the constants 27 and 297; divisions cleared; simple paths inside G⋆ of length ≤ h sharing a vertex with P; endpoints are vertices; reason: Lean convention, same statement
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 4.3 and its proof, pp.12–13

import Mathlib
import Definitions.Def_LCPlanarSteiner_IsSPath
import Definitions.Def_LCPlanarSteiner_plen
import Definitions.Def_LCPlanarSteiner_ArmsLE
import Definitions.Def_LCPlanarSteiner_pcost
import Definitions.Def_LCPlanarSteiner_Dlog
import Definitions.Def_LCPlanarSteiner_StrictForest
import Definitions.Def_LCPlanarSteiner_underlying
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace LCPlanarSteiner

/-- **Lemma 4.3 (Planar extraction), with its consequence (13).**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 4.3, pp.12–13: "A strict planar forest subgraph F⋆ serving r pairs has an original
subgraph G⋆, a directed path P ⊆ G⋆ of length at most h, and a nonempty pair set J with strict
original witnesses meeting P, such that c(G⋆)/|J| ≤ C_E D_r c(F⋆)/r, C_E = 27. Consequently, for
0 < η ≤ 1, some original junction satisfies (8) and c(H′)/|I| ≤ C_NE D_r²/(ηr) · OPT^F_h,
C_NE = 11C_E. (13)"

Let `G` be well-formed, `h > 0`, and `F⋆` a set of arcs with planar underlying graph in which each
of the `r ≥ 1` pairs `(s_i, t_i)` has a walk of length `≤ h`. Then:
1. there are an arc set `G⋆`, a simple directed path `P` inside `G⋆` with `ℓ(P) ≤ h`, a nonempty
   index set `J ⊆ [r]` and, for `i ∈ J`, simple paths `W_i` from `s_i` to `t_i` inside `G⋆` with
   `ℓ(W_i) ≤ h`, each meeting `P`, such that `c(G⋆)/|J| ≤ 27 D_r c(F⋆)/r`;
2. for every `0 < η ≤ 1` there is a junction `(H′, v, I)`, `I ⊆ [r]` nonempty, with
   `dist_{H′}(s_i, v) + dist_{H′}(v, t_i) ≤ (1 + η)h` for `i ∈ I` and
   `c(H′)/|I| ≤ 297 D_r² c(F⋆)/(ηr)`.

**Formalization Note.** The divisions are cleared (`c(G⋆) · r ≤ 27 D_r c(F⋆) |J|`). In (13),
`OPT^F_h` is replaced by `c(F⋆)` for the given strict planar forest `F⋆`; at an optimal `F⋆` this is
the printed bound. Pairs may be self-pairs. `h > 0` is the standing assumption of §§3–4 (p.5). -/
theorem lemma_4_3 (G : Net) (hG : G.WF) (h : ℚ) (hh : 0 < h) (dem : List (ℕ × ℕ))
    (hr : dem ≠ []) (hdem : ∀ d ∈ dem, d.1 < G.n ∧ d.2 < G.n) (Fs : Finset ℕ)
    (hF : StrictForest G dem h Fs)
    (hpl : RobertsonSeymour1986.GM5.IsPlanar (underlying G Fs)) :
    (∃ (Gs : Finset ℕ) (u₀ u₁ : ℕ) (P : List ℕ) (J : Finset ℕ) (W : ℕ → List ℕ),
      IsSPath G u₀ u₁ P ∧ (∀ e ∈ P, e ∈ Gs) ∧ plen G P ≤ h ∧
      J.Nonempty ∧ (∀ i ∈ J, i < dem.length) ∧
      (∀ i ∈ J, IsSPath G (dem.getD i (0, 0)).1 (dem.getD i (0, 0)).2 (W i) ∧
        (∀ e ∈ W i, e ∈ Gs) ∧ plen G (W i) ≤ h ∧
        ∃ x ∈ verts G (dem.getD i (0, 0)).1 (W i), x ∈ verts G u₀ P) ∧
      pcost G Gs * dem.length ≤ 27 * (Dlog dem.length : ℚ) * pcost G Fs * J.card) ∧
    ∀ η : ℚ, 0 < η → η ≤ 1 →
      ∃ (H' : Finset ℕ) (v : ℕ) (I : Finset ℕ), I.Nonempty ∧ (∀ i ∈ I, i < dem.length) ∧
        (∀ i ∈ I, ArmsLE G H' v (dem.getD i (0, 0)).1 (dem.getD i (0, 0)).2 ((1 + η) * h)) ∧
        pcost G H' * (η * dem.length) ≤
          297 * (Dlog dem.length : ℚ) ^ 2 * pcost G Fs * I.card := by sorry

end LCPlanarSteiner
