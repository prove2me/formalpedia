-- Prove2me | Theorems.Thm_GaoQuantumUnion_one_step_disturbance
-- name    : GaoQuantumUnion.one_step_disturbance
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-19T21:45:11.767834+00:00
-- url     : https://prove2.me/theorems/25b47f58-bc66-4bce-aa9e-4ddbbfa3a64d
-- title:
--   Lemma 1 — Squared trace-distance accumulation in one projection
-- statement:
--   For unit vectors $\psi,\phi$ and an orthogonal projector $P$, let $T_P$ denote the normalized projection of the rank-one state. If both normalization probabilities are positive,
--
--   $$D(\psi,T_P(\phi))^2\le D(\psi,\phi)^2+D(\psi,T_P(\psi))^2.$$
--
--   The distance is the unhalved trace distance of the corresponding rank-one matrices. This is Lemma 1 with the original vector and the preceding-step vector named explicitly; the positive hypotheses exclude only undefined projected vectors.
-- source:
--   Jingliang Gao, Quantum union bounds for sequential projective measurements, arXiv:1410.5688v2, Physical Review A 92, 052331 (2015), https://doi.org/10.1103/PhysRevA.92.052331; Lemma 1, PDF p. 7; the preceding vector definitions on pp. 5–6

import Definitions.Def_GaoQuantumUnion_Model
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false

namespace GaoQuantumUnion
theorem one_step_disturbance {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ φ : ι → ℂ) (hψ : IsUnitVector ψ) (hφ : IsUnitVector φ)
    (P : Matrix ι ι ℂ) (hP : IsProjector P)
    (hψq : 0 < successProb (fun _ : Fin 1 => P) (pureState ψ))
    (hφq : 0 < successProb (fun _ : Fin 1 => P) (pureState φ)) :
    (traceDist (pureState ψ) (postState (fun _ : Fin 1 => P) (pureState φ)))^2 ≤
      (traceDist (pureState ψ) (pureState φ))^2+
      (traceDist (pureState ψ) (postState (fun _ : Fin 1 => P) (pureState ψ)))^2 := by sorry
end GaoQuantumUnion
