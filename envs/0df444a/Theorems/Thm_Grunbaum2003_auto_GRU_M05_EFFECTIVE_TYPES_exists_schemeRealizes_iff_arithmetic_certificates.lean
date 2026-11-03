-- Prove2me | Theorems.Thm_Grunbaum2003_auto_GRU_M05_EFFECTIVE_TYPES_exists_schemeRealizes_iff_arithmetic_certificates
-- name    : Grunbaum2003.auto_GRU_M05_EFFECTIVE_TYPES_exists_schemeRealizes_iff_arithmetic_certificates
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T07:15:25.049967+00:00
-- url     : https://prove2.me/theorems/fc883672-e17e-4627-b760-7830992b1d41
-- title:
--   First-order real-field arithmetic characterization of vertex-face scheme realizability (M05)
-- statement:
--   This theorem establishes the first-order real-field arithmetic characterization of vertex-face scheme realizability (`∃ P : Set (Fin d → ℝ), SchemeRealizes k S P`) for the `GRU_M05_EFFECTIVE_TYPES` definition family.
--
--   For any dimension $d \in \mathbb{N}$, vertex count $k \in \mathbb{N}$, and scheme $S : \operatorname{List}(\operatorname{List} \mathbb{N})$, there exists a $d$-polytope $P \subseteq \mathbb{R}^d$ realizing $S$ if and only if there exists an injective configuration $V : \operatorname{Fin} k \to \mathbb{R}^d$ ($k > 0$) whose affine combinations span $\mathbb{R}^d$, whose vertices each admit a strict linear exposing functional $a \in \mathbb{R}^d$, whose row entries are bounded by $k$, and whose proper nonempty face-incidence sets $J \subseteq \{0, \dots, k - 1\}$ are exactly those admitting linear support certificates $(a, b) \in \mathbb{R}^d \times \mathbb{R}$ with
--   $$
--   \forall i \in \operatorname{Fin} k,\quad \sum_{t=0}^{d-1} a_t V_{i,t} \le b \quad\text{and}\quad \left(\sum_{t=0}^{d-1} a_t V_{i,t} = b \iff i \in J\right).
--   $$
--
--   **Formalization Note** This declaration provides the `Def_auto_GRU_M05_EFFECTIVE_TYPES_*` counterpart of `exists_schemeRealizes_iff_arithmetic_certificates`.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §5.5, pp. 90–91, Theorem 5.5.2

import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_IsDPolytope
import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_PolytopeFace
import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_SchemeRealizes
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem auto_GRU_M05_EFFECTIVE_TYPES_exists_schemeRealizes_iff_arithmetic_certificates (d k : ℕ)
    (S : List (List ℕ)) :
    (∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) ↔
    ∃ V : Fin k → Fin d → ℝ,
      0 < k ∧ Function.Injective V ∧
      (∀ x : Fin d → ℝ, ∃ w : Fin k → ℝ,
        (∑ i, w i) = 1 ∧ ∀ t : Fin d, (∑ i, w i * V i t) = x t) ∧
      (∀ i : Fin k, ∃ a : Fin d → ℝ, ∀ j : Fin k, j ≠ i →
        (∑ t, a t * V j t) < ∑ t, a t * V i t) ∧
      (∀ L ∈ S, ∀ n ∈ L, n < k) ∧
      ∀ J ∈ (Finset.range k).powerset,
        (∃ L ∈ S, L.toFinset = J) ↔
          J.Nonempty ∧ J ≠ Finset.range k ∧
            ∃ (a : Fin d → ℝ) (b : ℝ),
              (∀ i : Fin k, (∑ t, a t * V i t) ≤ b) ∧
              (∀ i : Fin k, (∑ t, a t * V i t) = b ↔ i.val ∈ J) := by sorry

end Grunbaum2003
