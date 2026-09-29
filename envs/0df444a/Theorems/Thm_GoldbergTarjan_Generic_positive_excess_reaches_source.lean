-- Prove2me | Theorems.Thm_GoldbergTarjan_Generic_positive_excess_reaches_source
-- name    : GoldbergTarjan.Generic.positive_excess_reaches_source
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:27:21.49058+00:00
-- url     : https://prove2.me/theorems/a7060013-5170-4902-be60-85403d937f0e
-- title:
--   Lemma 3.5 — from a vertex with positive excess the source is reachable in the residual graph
-- statement:
--   Let $N$ be a flow network with source $s$, let $f$ be a preflow and let $v$ be a vertex with positive excess, $e(v) = \sum_{u} f(u,v) > 0$. Then
--
--   $$s \text{ is reachable from } v \text{ in the residual graph } G_f.$$
--
--   Lemma 3.5 is the structural fact behind the label bound of Lemma 3.7: excess can always be returned to the source.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 926, Lemma 3.5

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Preflow

namespace GoldbergTarjan.Generic

/-- Lemma 3.5 (Goldberg–Tarjan 1988, p. 926). If `f` is a preflow and `v` is a vertex with
positive excess, then the source `s` is reachable from `v` in the residual graph `G_f`. -/
theorem positive_excess_reaches_source {V : Type} [Fintype V]
    (N : Network V) (f : V → V → ℝ) (v : V)
    (hf : IsPreflow N f) (hv : 0 < excess f v) :
    ResidualReachable N f v N.s := by sorry

end GoldbergTarjan.Generic
