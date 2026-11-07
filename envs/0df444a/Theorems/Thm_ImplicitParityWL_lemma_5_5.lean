-- Prove2me | Theorems.Thm_ImplicitParityWL_lemma_5_5
-- name    : ImplicitParityWL.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:17:43.011077+00:00
-- url     : https://prove2.me/theorems/dd60f2f5-2865-40e0-a504-54afd3f95b4b
-- title:
--   Lemma 5.5 — sweeping one stage
-- statement:
--   In the gadget of a schema $e$, fix an address $a\in\Sigma$ supported in $\mathfrak c_e$ and a stage $1\le h\le k+2$. Suppose that $k$ pebble pairs match
--   $$
--   \mathrm{trk}_{e,h-1,c}[0]\leftrightarrow\mathrm{trk}_{e,h-1,c}[b_c]\quad\text{for every }c\in\mathrm{supp}(a),
--   $$
--   so the observed value is $\sum_cb_c$. With one additional pebble pair and $O(k)$ moves, Spoiler can either win or reach a game state matching $\mathrm{trk}_{e,h,c}[0]\leftrightarrow\mathrm{trk}_{e,h,c}[t_c]$ for every $c\in\mathrm{supp}(a)$ with $\sum_ct_c=\sum_cb_c$. The same statement holds with the stage indices $h-1$ and $h$ interchanged.
--
--   This is the basic step of Spoiler's strategy: the observed value travels through a strip stage unchanged.
--
--   **Formalization Note** The constant in $O(k)$ is absolute. Track indices $0$ and $k+2$ are the endpoint vertices of the strip.
--
--   Differences from the source:
--   - encoding: O(k) moves → ∃ absolute C, Forces (C * k); reason: the constant is chosen before k, ℓ and the system
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Lemma 5.5, p.27

import Mathlib
import Definitions.Def_ImplicitParityWL_CompiledGraph

namespace ImplicitParityWL

/-- **Lemma 5.5** (Sweeping one stage; Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.27): in the gadget of a schema `e`, fix an address `a` supported in `𝔠_e`
and a stage `1 ≤ h ≤ k + 2`. If `k` pebble pairs match `trk_{e,h-1,c}[0] ↔ trk_{e,h-1,c}[b_c]` for every `c ∈ supp(a)`,
then with one additional pebble pair and `O(k)` moves Spoiler can either win or reach a state matching
`trk_{e,h,c}[0] ↔ trk_{e,h,c}[t_c]` for every `c ∈ supp(a)` with `∑ t_c = ∑ b_c`. The same holds with the stage indices
`h - 1` and `h` interchanged.

**Formalization Note** The constant `C` in `O(k)` is absolute: it is chosen before `k`, `ℓ` and the system. -/
theorem lemma_5_5 : ∃ C : ℕ, ∀ (k ℓ : ℕ), 3 ≤ k → 1 ≤ ℓ →
    ∀ {W E : Type} [Fintype W] [Fintype E] (I : ImplicitSystem k ℓ W E) (e : E) (a : Address k ℓ),
      a.supp ⊆ (I.schema e).dom → ∀ h : ℕ, 1 ≤ h → h ≤ k + 2 →
      ∀ (S : GameState (I.Vertex 0) (I.Vertex 1) (k + 1)) (b : Coord k ℓ → ZMod 2),
        (I.PebbleMatch S (I.trackFamily e (h - 1)) a b →
          Forces (I.graph 0) (I.graph 1) (C * k) S (fun S' => ∃ t : Coord k ℓ → ZMod 2,
            I.PebbleMatch S' (I.trackFamily e h) a t ∧ ∑ c ∈ a.supp, t c = ∑ c ∈ a.supp, b c)) ∧
        (I.PebbleMatch S (I.trackFamily e h) a b →
          Forces (I.graph 0) (I.graph 1) (C * k) S (fun S' => ∃ t : Coord k ℓ → ZMod 2,
            I.PebbleMatch S' (I.trackFamily e (h - 1)) a t ∧ ∑ c ∈ a.supp, t c = ∑ c ∈ a.supp, b c)) := by sorry

end ImplicitParityWL
