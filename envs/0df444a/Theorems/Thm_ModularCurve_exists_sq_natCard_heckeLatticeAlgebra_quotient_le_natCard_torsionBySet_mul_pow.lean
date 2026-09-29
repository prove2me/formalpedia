-- Prove2me | Theorems.Thm_ModularCurve_exists_sq_natCard_heckeLatticeAlgebra_quotient_le_natCard_torsionBySet_mul_pow
-- name    : ModularCurve.exists_sq_natCard_heckeLatticeAlgebra_quotient_le_natCard_torsionBySet_mul_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/6cac9982-5403-5d3d-8898-85a22fb12604
-- title:
--   Rank-two bound: Hecke quotients against I^m-torsion of J₀(N)
-- statement:
--   Fix $N \ge 1$ and write $\mathbb{T}^L =$ `heckeLatticeAlgebra N ∅` for the $\mathbb{Z}$-subalgebra of $\operatorname{End}_{\mathbb{Z}}$ of the lattice [`CuspForm.intLattice N 2`](def/CuspForm_IntegralStructure.html#L3) (the $\mathbb{Z}$-span of those weight-two cusp forms on $\Gamma_0(N)$ all of whose $q$-coefficients are integers) obtained as the image of the weight-two level-$N$ Hecke algebra `heckeAlgebra N 2 ∅` acting by restriction to that lattice. Assume $\mathbb{T}^L$ is a reduced ring. Let $q$ be a prime and let $I$ be an ideal of `HeckeAlg` $= \mathbb{Z}[x_\ell : \ell \text{ prime}]$, the polynomial ring over $\mathbb{Z}$ on indeterminates indexed by the primes, with $q \in I$. The assertion is the existence of a natural number $C$ such that for every $m$, the square of the order of $\mathbb{T}^L / (I^L)^m$ is at most the order of the subgroup of $J_0(N)(\overline{\mathbb{Q}})$ annihilated by every element of $I^m$, times $q^C$. Here $I^L$ is the image of $I$ under the ring map $\mathbb{Z}[x_\ell] \to \mathbb{T}^L$ sending $x_\ell$ to $U_\ell$ if $\ell \mid N$ and to $T_\ell$ otherwise (so the ideal occurring is the $m$-th power of the image of $I$), $J_0(N)(\overline{\mathbb{Q}})$ is the degree-zero divisor class group `JZero N` of the modular curve of level $N$ over $\overline{\mathbb{Q}}$, and the `HeckeAlg`-action on it is `heckeModuleBar N`, given by $x_\ell \mapsto$ `heckeOperatorBar N ℓ` when these correspondences commute and by the trivial action $x_\ell \mapsto 0$ otherwise; both cardinalities are `Nat.card`, so an infinite group contributes $0$.
--
--   This is the elementary half of the rank-two structure of the Hecke module $J_0(N)$: via the Eichler–Shimura uniformisation and the freeness of rational homology of rank two over the Hecke algebra, the order of a Hecke quotient is bounded, up to a power of $q$ independent of $m$, by the square root of the order of the corresponding $I^m$-torsion of the Jacobian. It feeds the comparison of $I^m$-torsion with toric torsion and reduction modulo $\ell$ used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_sq_natCard_heckeLatticeAlgebra_quotient_le_natCard_torsionBySet_mul_pow.lean

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve CuspForm

theorem ModularCurve.exists_sq_natCard_heckeLatticeAlgebra_quotient_le_natCard_torsionBySet_mul_pow
    (N : ℕ) [NeZero N] (hred : IsReduced ↥(heckeLatticeAlgebra N ∅))
    (q : ℕ) [Fact q.Prime] (I : Ideal HeckeAlg) (hqI : (q : HeckeAlg) ∈ I) :
    ∃ C : ℕ, ∀ m : ℕ,
      Nat.card (↥(heckeLatticeAlgebra N ∅) ⧸
          (Ideal.map ((latticeRestrictHom N ∅).toRingHom.comp (heckeEvalForms N 2)) I) ^ m) ^ 2 ≤
        Nat.card ↥(letI := heckeModuleBar N;
          Submodule.torsionBySet HeckeAlg (JZero N) (↑(I ^ m) : Set HeckeAlg)) * q ^ C := by sorry
