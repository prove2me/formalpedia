-- Prove2me | Theorems.Thm_MosonyiPetz_proposition_2
-- name    : MosonyiPetz.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:45:25.717904+00:00
-- url     : https://prove2.me/theorems/0ccabf82-9b47-48dd-80af-d32ecf55cc22
-- title:
--   Proposition 2: a unitary normalizing $\mathcal A$ commutes with every $P_m$
-- statement:
--   Let $\mathcal A$ be a unital $*$-subalgebra of $\mathcal B(\mathcal H)$ ($\mathcal H$ finite dimensional) and let $u$ be a unitary such that $a\mapsto u^*au$ maps $\mathcal A$ into $\mathcal A$. Then
--
--   $$uP_m=P_mu\qquad\text{for every multiplicity } m,$$
--
--   where $P_m$ is the sum of the minimal central projections of $\mathcal A$ whose block $M_d\otimes I_m$ has multiplicity $m$. Hence $u=\bigoplus_mP_muP_m$. This is the first reduction in the analysis of the unitaries $T(D_s)^{it}$ normalizing $\mathcal D_{\mathcal K}$.
--
--   **Formalization Note** $P_m$ is the intrinsic `multiplicityProjection` (multiplicity = rank of a minimal projection below the block); it is $0$ for multiplicities that do not occur. The coordinate form (9) is not assumed.
--
--   Differences from the source:
--   - reading: a subalgebra A of B(H) → A : StarSubalgebra ℂ (Matrix H H ℂ) (a unital *-subalgebra); reason: the decomposition (9) into full matrix blocks with projections P_{m,d} summing to the identity is that of a unital *-subalgebra
--   - encoding: u*Au ⊂ A for the unitary u → u ∈ Matrix.unitaryGroup and ∀ a ∈ A, star u * a * u ∈ A; reason: same condition
--   - encoding: P_m defined in the coordinates (9) → multiplicityProjection A m (sum of minimal central projections of multiplicity m); reason: the same projection, defined without choosing coordinates
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, §3, p.6, Proposition 2

import Mathlib
import Definitions.Def_MosonyiPetz_multiplicityProjection

open scoped Matrix

namespace MosonyiPetz

/-- **Proposition 2: a unitary normalizing a subalgebra commutes with every multiplicity
projection.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §3, p.6, Proposition 2: "Let u be a unitary in B(H) such that the map A ↦ u*Au leaves A
invariant. Then u commutes with Pm for every multiplicity m."

For a unital *-subalgebra `A` of `B(H)` and a unitary `u` with `u* a u ∈ A` for every `a ∈ A`,
`u P_m = P_m u` for every `m`, where `P_m` is the sum of the minimal central projections of `A`
whose block has multiplicity `m`.

**Formalization Note.** "Subalgebra" is a unital *-subalgebra (`StarSubalgebra`), as in the decomposition (9), whose
projections `P_{m,d}` sum to the identity. `P_m` is the intrinsic `multiplicityProjection`
(`P_m = 0` for a multiplicity that does not occur); the coordinate form (9) is not assumed. -/
theorem proposition_2 {H : Type*} [Fintype H] [DecidableEq H]
    (A : StarSubalgebra ℂ (Matrix H H ℂ)) (u : Matrix H H ℂ) (hu : u ∈ Matrix.unitaryGroup H ℂ)
    (hinv : ∀ a ∈ A, star u * a * u ∈ A) (m : ℕ) :
    u * multiplicityProjection A m = multiplicityProjection A m * u := by sorry

end MosonyiPetz
