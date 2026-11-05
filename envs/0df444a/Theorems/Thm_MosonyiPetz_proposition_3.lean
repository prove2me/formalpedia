-- Prove2me | Theorems.Thm_MosonyiPetz_proposition_3
-- name    : MosonyiPetz.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:30.494853+00:00
-- url     : https://prove2.me/theorems/531f6906-b266-4874-852d-b8bd7c552aa5
-- title:
--   Proposition 3: with equal multiplicities a normalizing unitary commutes with every $P_d$
-- statement:
--   Let $\mathcal A$ be a unital $*$-subalgebra of $\mathcal B(\mathcal H)$ all of whose blocks have the same multiplicity $m$ (the setting of p.6), and let $u$ be a unitary such that $a\mapsto u^*au$ maps $\mathcal A$ into $\mathcal A$. Then
--
--   1. $uP_d=P_du$ for every dimension $d$;
--   2. $u$ is block diagonal along the dimension projections:
--   $$u=\bigoplus_dP_duP_d=\sum_dP_duP_d.$$
--
--   Here $P_d$ is the sum of the minimal central projections whose block $z\mathcal A\cong M_d$ has dimension $d$. With Proposition 2 it reduces the description of $u$ to an algebra with one multiplicity and one dimension (Proposition 4).
--
--   **Formalization Note** $P_d$ is the intrinsic `dimensionProjection` ($0$ for dimensions that do not occur), and the sum over $d$ is a `finsum` over $\mathbb N$ with finitely many nonzero terms. The equal-multiplicity setting is the hypothesis that every minimal central projection has multiplicity $m$.
--
--   Differences from the source:
--   - reading: a subalgebra A of B(H) → A : StarSubalgebra ℂ (Matrix H H ℂ) (a unital *-subalgebra); reason: the decomposition (9) into full matrix blocks with projections P_{m,d} summing to the identity is that of a unital *-subalgebra
--   - encoding: u*Au ⊂ A for the unitary u → u ∈ Matrix.unitaryGroup and ∀ a ∈ A, star u * a * u ∈ A; reason: same condition
--   - encoding: P_d defined in the coordinates of p.6 → dimensionProjection A d (sum of minimal central projections of block dimension d); reason: the same projection, defined without choosing coordinates
--   - encoding: u = ⊕_d P_d u P_d → u = ∑ᶠ d : ℕ, P_d * u * P_d; reason: finite sum over the dimensions that occur; P_d = 0 otherwise
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, §3, pp.6–7, Proposition 3

import Mathlib
import Definitions.Def_MosonyiPetz_IsMinimalCentralProjection
import Definitions.Def_MosonyiPetz_multiplicity
import Definitions.Def_MosonyiPetz_dimensionProjection

open scoped Matrix

namespace MosonyiPetz

/-- **Proposition 3: with equal multiplicities, a normalizing unitary is block diagonal along the
dimension projections.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §3, pp.6–7, Proposition 3: "In the above setting u commutes with Pd for every dimension d, and
so u has the blockdiagonal structure u = ⊕_d PduPd." The setting (p.6): "we can restrict our
attention to the case when all the multiplicities are the same number m".

For a unital *-subalgebra `A` of `B(H)` all of whose minimal central projections have the same
multiplicity `m`, and a unitary `u` with `u* a u ∈ A` for every `a ∈ A`:
1. `u P_d = P_d u` for every `d`;
2. `u = Σ_d P_d u P_d`.

**Formalization Note.** `P_d` is the intrinsic `dimensionProjection` (sum of the minimal central
projections whose block `zA ≅ M_d` has dimension `d`, `0` if none). The sum over `d` is a
`finsum` over `ℕ`; only finitely many `P_d` are nonzero. -/
theorem proposition_3 {H : Type*} [Fintype H] [DecidableEq H]
    (A : StarSubalgebra ℂ (Matrix H H ℂ)) (m : ℕ)
    (hm : ∀ z, IsMinimalCentralProjection A z → multiplicity A z = m)
    (u : Matrix H H ℂ) (hu : u ∈ Matrix.unitaryGroup H ℂ)
    (hinv : ∀ a ∈ A, star u * a * u ∈ A) :
    (∀ d : ℕ, u * dimensionProjection A d = dimensionProjection A d * u) ∧
    u = ∑ᶠ d : ℕ, dimensionProjection A d * u * dimensionProjection A d := by sorry

end MosonyiPetz
