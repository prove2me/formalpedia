-- Prove2me | Theorems.Thm_NieYangPareto_epigraph_eq_add_orthant
-- name    : NieYangPareto.epigraph_eq_add_orthant
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:30.979451+00:00
-- url     : https://prove2.me/theorems/dce3c39b-65c6-425f-b26a-0162037e9221
-- title:
--   §3 after (3.1) — $\mathcal U=f(K)+\mathbb R^m_+$ and $\operatorname{conv}(\mathcal U)=\operatorname{conv}(f(K))+\mathbb R^m_+$
-- statement:
--   For the problem (1.1), with $\mathbb R^m_+$ the set of nonnegative vectors, the epigraph set and its convex hull are orthant sums:
--
--   $$
--   \mathcal U=f(K)+\mathbb R^m_+,\qquad \operatorname{conv}(\mathcal U)=\operatorname{conv}(f(K))+\mathbb R^m_+ .
--   $$
--
--   No hypothesis on $K$ is needed. This is the description of $\mathcal U$ used throughout §3.
--
--   Differences from the source:
--   - encoding: disjoint finite label sets ℰ, ℐ → two finite types E, I (`[Finite E] [Finite I]`), each with its own constraint family; reason: separate types encode disjointness; the same instances
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, §3 after (3.1), p.6

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_MOP_U
open Pointwise

namespace NieYangPareto

/-- **`𝒰 = f(K) + ℝ^m_+` and `conv(𝒰) = conv(f(K)) + ℝ^m_+`.** Nie–Yang, arXiv:2108.04336v2, §3 after
(3.1), p.6: "Then, 𝒰 = f(K) + ℝ^m_+ and its convex hull conv(𝒰) = conv(f(K)) + ℝ^m_+."

**Formalization Note** `ℝ^m_+` is `{q | 0 ≤ q}` in the pointwise order, and `+` is the pointwise sum
of sets. -/
theorem epigraph_eq_add_orthant {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I) :
    P.U = (P.obj '' P.K) + {q : Fin m → ℝ | 0 ≤ q} ∧
      convexHull ℝ P.U = convexHull ℝ (P.obj '' P.K) + {q : Fin m → ℝ | 0 ≤ q} := by sorry

end NieYangPareto
