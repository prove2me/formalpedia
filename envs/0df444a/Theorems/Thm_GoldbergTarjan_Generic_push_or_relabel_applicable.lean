-- Prove2me | Theorems.Thm_GoldbergTarjan_Generic_push_or_relabel_applicable
-- name    : GoldbergTarjan.Generic.push_or_relabel_applicable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:24:54.503024+00:00
-- url     : https://prove2.me/theorems/cc81efee-b568-4363-822e-c1cd793af92e
-- title:
--   Lemma 2.1 — at an active vertex either a push or a relabel applies
-- statement:
--   Let $N$ be a flow network, let $f$ be a preflow, let $d$ be a valid labeling for $f$, and let $v$ be an active vertex ($v \notin \{s,t\}$, $d(v) < \infty$, $e(v) > 0$). Then
--
--   $$\bigl(\exists\, w \in V:\ \text{Push}(v,w) \text{ is applicable}\bigr) \ \lor\ \text{Relabel}(v) \text{ is applicable}.$$
--
--   Lemma 2.1 links the two notions of termination: when no basic operation applies, there is no active vertex. It is used in the proof of Theorem 3.4.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 925, Lemma 2.1

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Operations

namespace GoldbergTarjan.Generic

/-- Lemma 2.1 (Goldberg–Tarjan 1988, p. 925). If `f` is a preflow, `d` is any valid labeling
for `f`, and `v` is any active vertex, then either a push or a relabel operation is applicable
to `v`. -/
theorem push_or_relabel_applicable {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V)
    (hf : IsPreflow N f) (hd : IsValidLabeling N f d) (hv : IsActive N f d v) :
    (∃ w, PushApplicable N f d v w) ∨ RelabelApplicable N f d v := by sorry

end GoldbergTarjan.Generic
