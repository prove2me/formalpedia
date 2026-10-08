-- Prove2me | Theorems.Thm_LeightonRao_ShortPaths_lemma_19
-- name    : LeightonRao.ShortPaths.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:26:23.106991+00:00
-- url     : https://prove2.me/theorems/3a33e98e-489f-4598-aa84-b9921c49a6f8
-- title:
--   Lemma 19, p. 808 — partition with edge and distance radii
-- statement:
--   Let $G$ be a connected capacitated graph on $n\ge2$ vertices, with total capacity $C$. Let $d$ be a nonnegative symmetric edge-length function with positive total weight $W=\sum_e C(e)d(e)$, and let $\Delta>0$. There is a partition of $V$ into components such that each component has one center and paths within that component witnessing both radii, and
--
--   $$\text{edge radius}\le\frac{\Delta C}{W},\qquad
--     \text{distance radius}\le\Delta,\qquad
--     \text{capacity between components}\le\frac{4W\log_2 n}{\Delta}.$$
--
--   The partition supplies the simultaneous path-length and distance control used in the short-path result.
--
--   **Formalization Note** The paper's standing connectivity convention is explicit. The added condition $W>0$ makes its division by $W$ meaningful; at $W=0$, Lean's real division would incorrectly give radius zero. A single internal walk witnesses both radii.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 808, Lemma 19

import Mathlib
import Definitions.Def_LeightonRao_ShortPaths_Setting

namespace LeightonRao.ShortPaths

/-- Lemma 19, p. 808. The positivity of W makes the paper's radius ΔC/W meaningful. -/
theorem lemma_19 {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (Δ : ℝ) (hΔ : 0 < Δ) (hW : 0 < totalWeight N d) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ S ∈ P.parts, HasRadii N d S (Δ * totalCap N / totalWeight N d) Δ) ∧
      crossCap N P ≤ 4 * totalWeight N d *
        Real.logb 2 (Fintype.card V : ℝ) / Δ := by sorry

end LeightonRao.ShortPaths
