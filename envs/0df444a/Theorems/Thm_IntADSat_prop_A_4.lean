-- Prove2me | Theorems.Thm_IntADSat_prop_A_4
-- name    : IntADSat.prop_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:37.171521+00:00
-- url     : https://prove2.me/theorems/546fa469-f5d6-4d2c-a176-d7edc35d7a71
-- title:
--   Proposition A.4 — invariant obstruction
-- statement:
--   Let $k$ be any field and $G$ a simple graph on $[n]$, with adjacency and degree matrices $A,D$ reduced into $k$ and $e=(1,\dots,1)$. The module $k\langle A,D\rangle e$ is proper if and only if there is a nonzero subspace $W\subseteq k^n$ with
--
--   $$
--   W\subseteq e^\perp,\qquad AW\subseteq W,\qquad DW\subseteq W ,
--   $$
--
--   where $e^\perp=\{w:\sum_i w_i=0\}$ for the standard (nondegenerate) dot product. It converts failure of cyclicity into a common invariant subspace, the object bounded in Sections S1–S3.
--
--   Differences from the source:
--   - encoding: W ⊆ e^⊥ → ∑ᵢ wᵢ = 0 for every w ∈ W; reason: e^⊥ for the standard dot product
--   - encoding: any field k → any field K : Type (universe 0); reason: Lean universe convention of the published wordEval; every field of the paper lives there
--   - generalization: graphs with at least one vertex → every n, including n = 0; reason: at n = 0 both sides are false; specializes to n ≥ 1
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Proposition A.4, p.12 (PDF 13)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra
import Definitions.Def_IntADSat_wordModule

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat

/-- **Proposition A.4 (Invariant obstruction)** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.12 (PDF 13)). Over any field `K`, the module
`K⟨A, D⟩e` is proper if and only if there is a nonzero subspace `W ⊆ e^⊥` with `AW ⊆ W` and `DW ⊆ W`.

**Formalization Note** `A`, `D` are the adjacency and degree matrices of `G` reduced into `K`;
`W ⊆ e^⊥` is `∑ᵢ wᵢ = 0` for every `w ∈ W`. -/
theorem prop_A_4 (K : Type) [Field K] {n : ℕ} (G : SimpleGraph (Fin n)) :
    wordModule K G ≠ ⊤ ↔
      ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ w ∈ W, ∑ i, w i = 0) ∧
        (∀ w ∈ W, ((adjacency G).map (Int.cast : ℤ → K)).mulVec w ∈ W) ∧
        (∀ w ∈ W, ((degreeMatrix G).map (Int.cast : ℤ → K)).mulVec w ∈ W) := by sorry

end IntADSat
