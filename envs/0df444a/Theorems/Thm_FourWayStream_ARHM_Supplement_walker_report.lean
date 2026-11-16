-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_walker_report
-- name    : FourWayStream.ARHM.Supplement.walker_report
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:10:27.228173+00:00
-- url     : https://prove2.me/theorems/9b9c5d84-af01-4868-8a71-fdacf1ad8a29
-- title:
--   Lemma E.2 — what a walker can report: on a cycle it closes only with $\ell=L$; on a path it never closes
-- statement:
--   In any graph of maximum degree two, consider a walker processing any sequence of edges of the graph (repetitions allowed).
--   1. If it starts on a cycle of length $L\ge3$, it moves along that cycle in one direction: there is a direction such that after $\ell$ moves it is at the vertex $\ell$ steps from its start in that direction, $\ell\le L$, and if it closes, it closes with $\ell=L$.
--   2. If it starts on a path, it never closes.
--
--   This is the deterministic fact behind the walker algorithm of Theorem 7.11: a walker never reports a wrong cycle length.
--
--   **Formalization Note** The cycle is an injective labeling $c:\mathbb Z/L\to[n]$ with every $\{c_i,c_{i+1}\}$ an edge, the walker starting at $c_0$; the path is an injective labeling of a whole component. The statement is checked after every prefix of the edge sequence.
--
--   Differences from the source:
--   - encoding: a walker processing an arriving stream → the walker run on every prefix of every finite sequence of edges of the graph; reason: the walker is deterministic, so this is the same claim for every stream
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.49, Lemma E.2 (proof p.50)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Supplement_NGC
import Definitions.Def_FourWayStream_ARHM_Supplement_Walker

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Lemma E.2 (What a walker can report), p.49. In any graph of maximum degree two, on any sequence
of its edges (repetitions allowed), a walker started on a cycle of length `L ≥ 3` moves along that
cycle in one direction — after `ℓ` moves it is `ℓ` steps from its start in a fixed direction — and if
it closes, it closes with `ℓ = L`. A walker started on a path never closes. -/
theorem walker_report (n : ℕ) (E : Finset (Sym2 (Fin n))) (hE : MaxDegTwo E) :
    (∀ (L : ℕ) (cyc : ZMod L → Fin n), IsCycleOf E L cyc →
      ∀ str : List (Sym2 (Fin n)), (∀ e ∈ str, e ∈ E) →
        ∃ dir : Bool, ∀ i ≤ str.length,
          (walk (cyc 0) (str.take i)).cur = cycPos cyc dir (walk (cyc 0) (str.take i)).steps ∧
          (walk (cyc 0) (str.take i)).steps ≤ L ∧
          ((walk (cyc 0) (str.take i)).closed = true → (walk (cyc 0) (str.take i)).steps = L)) ∧
    (∀ (P : ℕ) (pth : Fin P → Fin n), IsPathComponentOf E P pth → ∀ j : Fin P,
      ∀ str : List (Sym2 (Fin n)), (∀ e ∈ str, e ∈ E) → (walk (pth j) str).closed = false) := by sorry

end FourWayStream.ARHM.Supplement
