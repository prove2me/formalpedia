-- Prove2me | Theorems.Thm_MatMulPolyBarrier_Operational_definition_5_5_well_defined
-- name    : MatMulPolyBarrier.Operational.definition_5_5_well_defined
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:08:24.276885+00:00
-- url     : https://prove2.me/theorems/0648b099-2ee8-41b9-86a3-11e8b32984b6
-- title:
--   Definition 5.5(i) — $F^\star_\theta(d_1,d_2,d_3)$ does not depend on the choice of the indices $i,j,k$
-- statement:
--   Let $\theta\in\Theta$ and let $(d_1,d_2,d_3)$ be an admissible triple of real numbers, with $A_s=(d_s-\theta_s)/(1-\theta_s)$. For **every** choice of indices with $\{i,j,k\}=\{1,2,3\}$, $d_i\le d_k$, $d_j\le d_k$ and $A_i\le A_j$,
--   $$F^\star_\theta(d_1,d_2,d_3)=A_i^{\,1-p_i}\bigl(\theta_jA_i+(1-\theta_j)A_j\bigr)^{p_i}.$$
--   So Definition 5.5(i) is well defined: the paper notes that if two entries are largest the third is $1$, so $i$ is its index and both choices of $k$ give $\max(d_1,d_2,d_3)^{p_i}$, and that if $A_i=A_j$ both choices of $i$ give $A_i$. The Lean definition of $F^\star_\theta$ computes the value with one fixed choice; this theorem says every other admissible choice gives the same number.
--
--   Differences from the source:
--   - encoding: indices i, j, k ∈ {1, 2, 3} with {i, j, k} = {1, 2, 3} → i j k : Fin 3 pairwise distinct (0-based); reason: Lean indexing, same instances
--   - reading: "the value does not depend on the choice of the indices" → for every admissible choice, the formula equals FstarTriple θ d (the value at the fixed choice of the definition); the justifying remarks after the colon are not separate conjuncts; reason: a Lean function must fix one choice, and independence is exactly agreement of every choice with it; the remarks are the paper's argument for that claim
-- source:
--   Amanov, van den Berg, Zuiddam, Multiplying matrices via polynomials: operational asymptotic spectrum barrier, STOC 2027 submission (manuscript sha256 38bd5183…), p. 38, Definition 5.5(i) (well-definedness remark)

import Mathlib
import Definitions.Def_MatMulPolyBarrier_Operational_FExpr
import Definitions.Def_MatMulPolyBarrier_Operational_Fstar

set_option autoImplicit false

namespace MatMulPolyBarrier.Operational

/-- Definition 5.5(i), p. 38: the value of `F⋆_θ(d₁, d₂, d₃)` does not depend on the choice of the
indices: for every admissible triple `d` and every choice of distinct indices `i, j, k` with
`d i, d j ≤ d k` and `A_i ≤ A_j`, the formula `A_i^{1 − p_i} (θ_j A_i + (1 − θ_j) A_j)^{p_i}` gives the
value of `F⋆_θ(d)` (which the definition computes with one fixed choice). -/
theorem definition_5_5_well_defined (θ : Fin 3 → ℝ) (hθ : InTheta θ) (d : Fin 3 → ℝ)
    (hd : IsAdmissible (d 0) (d 1) (d 2)) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hdi : d i ≤ d k) (hdj : d j ≤ d k) (hA : Acoord θ d i ≤ Acoord θ d j) :
    FstarTriple θ d =
      Acoord θ d i ^ (1 - pExp θ i) *
        (θ j * Acoord θ d i + (1 - θ j) * Acoord θ d j) ^ pExp θ i := by sorry

end MatMulPolyBarrier.Operational
