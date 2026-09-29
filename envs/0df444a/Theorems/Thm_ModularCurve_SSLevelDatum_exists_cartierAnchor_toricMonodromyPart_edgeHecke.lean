-- Prove2me | Theorems.Thm_ModularCurve_SSLevelDatum_exists_cartierAnchor_toricMonodromyPart_edgeHecke
-- name    : ModularCurve.SSLevelDatum.exists_cartierAnchor_toricMonodromyPart_edgeHecke
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/033acf5a-bbcc-57e5-a034-6ce5bed6beb3
-- title:
--   Hecke-equivariant character duality for the q-adic toric part
-- statement:
--   Let $N,q,q'$ be non-zero natural numbers with $q$ and $q'$ prime, $q\nmid N$, $q'\nmid N$ and $q'\neq q$, and let $A$ be a valuation subring of an algebraic closure of $\mathbb{Q}$ satisfying `LiesOverPrime q`, i.e. $q$ lies in the non-units of $A$; write $\kappa$ for the residue field of $A$, assumed of characteristic $q$, and assume the set `ssPlaces q (N * q') κ` of supersingular places of the level-$Nq'$ modular function field over $\kappa$ is finite. Let $X$ be an `SSLevelDatum q κ N q'`, that is, the package consisting of the two $j$-membership conditions at levels $N$ and $q'$, integrality of the two level-degeneracy maps and of all Hecke legs, the statements that restriction along either degeneracy map carries supersingular places of level $Nq'$ to supersingular places of level $N$, an Atkin–Lehner level automorphism together with its defining property and the stability of the supersingular places under it, and modular polynomial data satisfying a Kronecker congruence. Let $n_1:\{\text{primes}\}\to\mathbb{Z}$ be such that for every prime $\ell$ the transpose of the supersingular Hecke matrix `X.edgeHecke ℓ` has all row sums equal to $n_1(\ell)$. Equip $J=$ `JZero (N * q' * q)`, the degree-zero Picard group of the level-$Nq'q$ modular function field over the algebraic closure of $\mathbb{Q}$, with the Hecke-algebra module structure `heckeModuleBar (N * q' * q)`. Then there is an isomorphism of additive groups $\varepsilon$ from `toricMonodromyPart q (A.inertiaSubgroupIn ℚ)`, the Hecke-submodule of $J$ spanned by the elements $\sigma\cdot x-x$ with $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ and $x$ annihilated by some positive integer coprime to $q$, onto the group of additive homomorphisms from the character lattice of `ssPlaces q (N * q') κ` (the kernel of the degree map on $\mathbb{Z}$-valued divisors) to $\kappa^{\times}$ written additively, such that for every prime $\ell$, every $y$ in the toric monodromy part and every $x$ in the character lattice, $\varepsilon(\mathrm{heckeGen}\,\ell\cdot y)(x)=\varepsilon(y)\bigl(\mathrm{heckeCharacterAction}\,(\mathrm{X.edgeHecke}\,\ell)^{t}\,x\bigr)$.
--
--   This is the Hecke-equivariant character (Cartier) duality identifying the $q$-adic toric monodromy part of the Jacobian of level $Nq'q$ with the group of $\kappa^{\times}$-valued characters of the degree-zero supersingular divisor lattice of level $Nq'$, the Hecke action on the second factor being given by the transposed supersingular Hecke matrices of the two-level datum. It is used in the comparison of ranks underlying level lowering at $q$, namely in the bounds `finrank_span_toricMonodromyPart_le_finrank_quotient_old_add_ribbon_of_ssLevelDatum` and its variant under a divisibility hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSLevelDatum_exists_cartierAnchor_toricMonodromyPart_edgeHecke.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.SSLevelDatum.exists_cartierAnchor_toricMonodromyPart_edgeHecke
    {N q q' : ℕ} [NeZero N] [NeZero q] [NeZero q'] [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) q]
    [Fintype ↥(ssPlaces q (N * q') (IsLocalRing.ResidueField ↥A))]
    (X : SSLevelDatum q (IsLocalRing.ResidueField ↥A) N q')
    (n₁ : Nat.Primes → ℤ) (hcol₁ : ∀ ℓ : Nat.Primes, HeckeRowSums (X.edgeHecke ℓ).transpose (n₁ ℓ)) :
    letI := heckeModuleBar (N * q' * q)
    ∃ ε : ↥(toricMonodromyPart (J := JZero (N * q' * q)) q (A.inertiaSubgroupIn ℚ)) ≃+
        (↥(characterLattice ↥(ssPlaces q (N * q') (IsLocalRing.ResidueField ↥A))) →+
          Additive (IsLocalRing.ResidueField ↥A)ˣ),
      ∀ (ℓ : Nat.Primes)
        (y : ↥(toricMonodromyPart (J := JZero (N * q' * q)) q (A.inertiaSubgroupIn ℚ)))
        (x : ↥(characterLattice ↥(ssPlaces q (N * q') (IsLocalRing.ResidueField ↥A)))),
        ε (heckeGen ℓ • y) x = ε y (heckeCharacterAction (X.edgeHecke ℓ).transpose (hcol₁ ℓ) x) := by sorry
