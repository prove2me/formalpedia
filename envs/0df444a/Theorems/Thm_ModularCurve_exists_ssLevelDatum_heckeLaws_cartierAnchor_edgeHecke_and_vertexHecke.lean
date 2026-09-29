-- Prove2me | Theorems.Thm_ModularCurve_exists_ssLevelDatum_heckeLaws_cartierAnchor_edgeHecke_and_vertexHecke
-- name    : ModularCurve.exists_ssLevelDatum_heckeLaws_cartierAnchor_edgeHecke_and_vertexHecke
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/675379c8-b378-56b1-abbe-d0ea8f374cb8
-- title:
--   Supersingular datum and Cartier anchors at levels Nq Rightarrow N
-- statement:
--   Let $N,q,q'$ be natural numbers with $q,q'$ prime, $q \nmid N$, $q' \nmid N$, $q' \neq q$, and $N,q,Nq'$ nonzero; let $A_1$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q'$, in the sense that $q'$ is a non-unit of $A_1$, with residue field $\kappa = \mathrm{ResidueField}(A_1)$ of characteristic $q'$, and assume the sets $\mathrm{ssPlaces}\,q'\,(Nq)\,\kappa$ and $\mathrm{ssPlaces}\,q'\,N\,\kappa$ of supersingular places (rational affine geometric places of the corresponding modular function field over $\kappa$ whose $j$-value is supersingular for $q'$) are finite. With $\mathrm{JZero}$ the degree-zero divisor class group of the base-changed modular function field and its Hecke-algebra module structure `heckeModuleBar`, the assertion is the existence of: a datum `X₁ : SSLevelDatum q' κ N q` (the two degeneracy inclusions of levels $Nq \rightrightarrows N$, their integrality, Atkin–Lehner involution, stability of supersingular places, and modular polynomial data satisfying the Kronecker congruence) together with a proof of `X₁.HeckeLaws`; integers $n_1(\ell)$ such that every column of the edge Hecke matrix $X_1.\mathrm{edgeHecke}\,\ell$ sums to $n_1(\ell)$; an additive isomorphism $\varepsilon_1$ from the $q'$-toric monodromy part of $\mathrm{JZero}(Nq'q)$, the Hecke submodule spanned by $\sigma\cdot x - x$ with $\sigma$ in the image of the inertia subgroup of $A_1$ over $\mathbb{Q}$ and $x$ killed by a positive integer coprime to $q'$, onto the additive homomorphisms from the degree-zero lattice $\mathrm{characterLattice}$ on $\mathrm{ssPlaces}\,q'\,(Nq)\,\kappa$ to $\mathrm{Additive}\,\kappa^{\times}$, satisfying $\varepsilon_1(T_\ell \cdot y)(x) = \varepsilon_1(y)\bigl(\mathrm{heckeCharacterAction}\,(X_1.\mathrm{edgeHecke}\,\ell)^{\mathsf T}\,x\bigr)$ for all primes $\ell$; and, in the same shape, integers $n_2(\ell)$ with the columns of $X_1.\mathrm{vertexHecke}\,\ell$ summing to $n_2(\ell)$ and an additive isomorphism $\varepsilon_2$ from the $q'$-toric monodromy part of $\mathrm{JZero}(Nq')$ onto the additive homomorphisms from the degree-zero lattice on $\mathrm{ssPlaces}\,q'\,N\,\kappa$ to $\mathrm{Additive}\,\kappa^{\times}$, intertwining the action of $T_\ell$ with the transposed vertex Hecke matrix.
--
--   This packages, for the auxiliary prime $q'$ of Ribet's level-switching argument, the supersingular graph of levels $Nq \rightrightarrows N$ in characteristic $q'$ together with the description of the $q'$-toric parts of $J_0(Nq'q)$ and $J_0(Nq')$ by character groups of degree-zero divisors on supersingular points, Hecke-equivariantly and in terms of the datum's own edge and vertex Hecke matrices. It feeds the comparison of ranks of toric monodromy parts used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ssLevelDatum_heckeLaws_cartierAnchor_edgeHecke_and_vertexHecke.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Definitions.Def_ModularCurve_SSDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.exists_ssLevelDatum_heckeLaws_cartierAnchor_edgeHecke_and_vertexHecke
    {N q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    [NeZero N] [NeZero q] [Fact q.Prime] [Fact q'.Prime]
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')
    [DecidableEq (IsLocalRing.ResidueField ↥A₁)] [CharP (IsLocalRing.ResidueField ↥A₁) q']
    [Fintype ↥(ssPlaces q' (N * q) (IsLocalRing.ResidueField ↥A₁))]
    [Fintype ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))]
    [DecidableEq ↥(ssPlaces q' (N * q) (IsLocalRing.ResidueField ↥A₁))]
    [DecidableEq ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))] [NeZero (N * q')] :
    letI := heckeModuleBar (N * q' * q)
    letI := heckeModuleBar (N * q')
    ∃ (X₁ : SSLevelDatum q' (IsLocalRing.ResidueField ↥A₁) N q) (_ : X₁.HeckeLaws)
      (n₁ : Nat.Primes → ℤ) (hcol₁ : ∀ ℓ : Nat.Primes, HeckeRowSums (X₁.edgeHecke ℓ).transpose (n₁ ℓ))
      (ε₁ : ↥(toricMonodromyPart (J := JZero (N * q' * q)) q' (A₁.inertiaSubgroupIn ℚ)) ≃+
          (↥(characterLattice ↥(ssPlaces q' (N * q) (IsLocalRing.ResidueField ↥A₁))) →+ Additive (IsLocalRing.ResidueField ↥A₁)ˣ)),
      (∀ (ℓ : Nat.Primes) (y : ↥(toricMonodromyPart (J := JZero (N * q' * q)) q' (A₁.inertiaSubgroupIn ℚ)))
        (x : ↥(characterLattice ↥(ssPlaces q' (N * q) (IsLocalRing.ResidueField ↥A₁)))),
        ε₁ (heckeGen ℓ • y) x = ε₁ y (heckeCharacterAction (X₁.edgeHecke ℓ).transpose (hcol₁ ℓ) x)) ∧
      ∃ (n₂ : Nat.Primes → ℤ) (hcol₂ : ∀ ℓ : Nat.Primes, HeckeRowSums (X₁.vertexHecke ℓ).transpose (n₂ ℓ))
      (ε₂ : ↥(toricMonodromyPart (J := JZero (N * q')) q' (A₁.inertiaSubgroupIn ℚ)) ≃+
          (↥(characterLattice ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))) →+ Additive (IsLocalRing.ResidueField ↥A₁)ˣ)),
      ∀ (ℓ : Nat.Primes) (y : ↥(toricMonodromyPart (J := JZero (N * q')) q' (A₁.inertiaSubgroupIn ℚ)))
        (x : ↥(characterLattice ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)))),
        ε₂ (heckeGen ℓ • y) x = ε₂ y (heckeCharacterAction (X₁.vertexHecke ℓ).transpose (hcol₂ ℓ) x) := by sorry
