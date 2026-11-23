-- Prove2me | Theorems.Thm_GaoQuantumUnion_decoder_bound
-- name    : GaoQuantumUnion.decoder_bound
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-19T21:46:57.091374+00:00
-- url     : https://prove2.me/theorems/09907df0-4d27-4325-9042-02f6a2f72e90
-- title:
--   Equation (26) — Sequential decoding effect lower bound
-- statement:
--   Let $P,Q_i$ be orthogonal projectors. At position $m$, first pass $P$, then reject candidates $0$ through $m-1$, then accept $Q_m$. For the resulting effect $\Lambda_m$,
--
--   $$\Lambda_m\succeq P-4P(I-Q_m)P-4\sum_{i<m}PQ_iP.$$
--
--   The rejection order is fixed by the actual chronological experiment, and only the strict prefix $i<m$ enters the sum.
-- source:
--   Jingliang Gao, Quantum union bounds for sequential projective measurements, arXiv:1410.5688v2, Physical Review A 92, 052331 (2015), https://doi.org/10.1103/PhysRevA.92.052331; Equation (26), PDF p. 13, with zero-based candidate indices

import Definitions.Def_GaoQuantumUnion_Decoding
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false

namespace GaoQuantumUnion
theorem decoder_bound {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (P : Matrix ι ι ℂ) (hP : IsProjector P) (Q : Fin M → Matrix ι ι ℂ)
    (hQ : ∀ i, IsProjector (Q i)) (m : Fin M) :
    (decoderEffect P Q m-(P-(4 : ℂ) • (P*(1-Q m)*P)-
      (4 : ℂ) • ∑ i ∈ Finset.univ.filter (fun i : Fin M => i.val < m.val), P*Q i*P)).PosSemidef := by sorry
end GaoQuantumUnion
