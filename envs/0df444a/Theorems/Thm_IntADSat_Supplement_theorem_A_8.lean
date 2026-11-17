-- Prove2me | Theorems.Thm_IntADSat_Supplement_theorem_A_8
-- name    : IntADSat.Supplement.theorem_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:56:36.668241+00:00
-- url     : https://prove2.me/theorems/ef07ce77-97dc-46d4-9e00-f8cabd9d4038
-- title:
--   Theorem A.8 — finite pointed reconstruction: $G\equiv_\mu H$ iff moments agree up to length $2n-1$ iff a rational orthogonal pointed intertwiner exists
-- statement:
--   Let $G$ be an AD-full graph of order $n\ge1$, i.e. $\dim_{\mathbb Q}\mathbb Q\langle A_G,D_G\rangle e=n$, and let $H$ be any finite simple graph. The following are equivalent:
--
--   1. $G\equiv_\mu H$, i.e. $\mu_G(w)=\mu_H(w)$ for every word $w$;
--   2. the principal moments agree for all words of length at most $2n-1$;
--   3. there is a rational orthogonal matrix $Q$ such that
--   $$Qe=e,\qquad QA_G=A_HQ,\qquad QD_G=D_HQ .$$
--
--   For fixed labelled graphs this matrix is unique, and $H$ is AD-full.
--
--   The theorem identifies moment equivalence on the AD-full locus with pointed rational orthogonal equivalence and gives a finite certificate for it.
--
--   Differences from the source:
--   - encoding: G AD-full of order n; graphs have at least one vertex → finrank ℚ (wordModule ℚ G) = n and 0 < n; reason: definition of AD-full (Definition A.1) and the standing assumption (p.11)
--   - encoding: H a finite simple graph; Q a rational orthogonal matrix → H : SimpleGraph (Fin m), any m; Q : m × n rational with QᵀQ = 1 and QQᵀ = 1; reason: orthogonality of a non-square matrix is impossible, so this is the paper's square orthogonal Q; m = n is not assumed
--   - reading: for fixed labelled graphs this matrix is unique, and H is AD-full → under condition (1): ∃! Q satisfying (3), and finrank ℚ (wordModule ℚ H) = m; reason: the sentence follows the list of equivalent conditions and is asserted when they hold
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem A.8, pp.13–14 (PDF 14–15)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra
import Definitions.Def_IntADSat_wordModule
import Definitions.Def_IntADSat_Supplement_moment
import Definitions.Def_IntADSat_Supplement_MomentEquiv
import Definitions.Def_IntADSat_Supplement_IsPointedIntertwiner

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat.Supplement

/-- **Theorem A.8 (Finite pointed reconstruction)** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), pp.13–14 (PDF 14–15)). Suppose `G` is AD-full of
order `n`. The following are equivalent: (1) `G ≡_μ H`; (2) the principal moments agree for all words of
length at most `2n − 1`; (3) there is a rational orthogonal matrix `Q` such that `Qe = e`, `QA_G = A_HQ`,
`QD_G = D_HQ`. For fixed labelled graphs this matrix is unique, and `H` is AD-full.

**Formalization Note** AD-full is `dim_ℚ M_ℚ(G) = n`. `H` is any finite simple graph, on `Fin m` for any `m`;
`Q` is an `m × n` rational matrix with `QᵀQ = 1`, `QQᵀ = 1` (orthogonality forces `m = n`, not assumed).
Uniqueness and AD-fullness of `H` are stated under the (equivalent) conditions, via (1). -/
theorem theorem_A_8 {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) (hn : 0 < n)
    (hG : Module.finrank ℚ (IntADSat.wordModule ℚ G) = n) :
    List.TFAE
      [MomentEquiv G H,
       ∀ w : Word, w.length ≤ 2 * n - 1 → moment G w = moment H w,
       ∃ Q : Matrix (Fin m) (Fin n) ℚ, IsPointedIntertwiner G H Q] ∧
    (MomentEquiv G H →
      (∃! Q : Matrix (Fin m) (Fin n) ℚ, IsPointedIntertwiner G H Q) ∧
      Module.finrank ℚ (IntADSat.wordModule ℚ H) = m) := by sorry

end IntADSat.Supplement
