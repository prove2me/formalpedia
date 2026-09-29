-- Prove2me | Theorems.Thm_ModularCurve_exists_cartierAnchor_toricMonodromyPart_ssHeckeFamilyC
-- name    : ModularCurve.exists_cartierAnchor_toricMonodromyPart_ssHeckeFamilyC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/911469e3-eee6-56a1-9e15-34a0c26b7593
-- title:
--   Cartier anchor of the toric part of J₀(Lp)
-- statement:
--   Fix a prime $p$, nonzero naturals $L$ and $Lp$ with $Lp = L\cdot p$ and $p \nmid L$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa =$ `IsLocalRing.ResidueField A` has characteristic $p$ and for which the set $\Sigma =$ `ssPlaces p L κ` of supersingular places of `modularFunctionFieldC κ L` is finite. Let `data : ModularPolynomialData p` be a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(p)$ vanishing at $(j(q), j(q^p))$, satisfying the Kronecker congruence $\Phi \equiv (X^p - Y)(X - Y^p)$ mod $p$, and assume for every nonzero $\ell$ that both degeneracy maps `heckeAlphaC κ L ℓ` and `heckeBetaC κ L ℓ` into the level-$\ell$ roof are integral. Give `JZero Lp` its `heckeModuleBar` Hecke-algebra structure. Then there are integers $n_\ell$ ($\ell$ prime), witnesses that the transpose of `ssHeckeFamilyC p κ L data hKr hlegs ℓ` (the Frobenius matrix for $\ell = p$, the $\alpha_*\beta^*$ matrix otherwise) has all row sums equal to $n_\ell$, and an additive isomorphism $\varepsilon$ from `toricMonodromyPart p (A.inertiaSubgroupIn ℚ)` — the Hecke submodule of `JZero Lp` spanned by $\sigma\cdot x - x$ with $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$ and $x$ killed by a positive integer coprime to $p$ — onto $\mathrm{Hom}(X_\Sigma, \mathrm{Additive}\,\kappa^\times)$, where $X_\Sigma$ is the degree-zero sublattice of $\mathbb{Z}[\Sigma]$, such that $\varepsilon(T_\ell\cdot y)(x) = \varepsilon(y)$ evaluated at the image of $x$ under `heckeCharacterAction` of the transposed matrix, for all primes $\ell$, and $n_\ell = \ell + 1$ whenever $\ell \nmid Lp$.
--
--   This is the Hecke-equivariant identification of the $p$-adic toric (monodromy) part of $J_0(Lp)$ with the character group of the supersingular module of level $L$, in the form used for level lowering at $p$. It is invoked in the two-level supersingular degeneracy results on edge and vertex Hecke matrices and in the analysis of torsion in the toric part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_cartierAnchor_toricMonodromyPart_ssHeckeFamilyC.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Definitions.Def_ModularCurve_SSDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open ModularCurve

theorem ModularCurve.exists_cartierAnchor_toricMonodromyPart_ssHeckeFamilyC
    (p : ℕ) [Fact p.Prime] (L Lp : ℕ) [NeZero L] [NeZero Lp] (hL : Lp = L * p) (hpL : ¬ p ∣ L)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    [Fintype ↥(ssPlaces p L (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces p L (IsLocalRing.ResidueField ↥A))]
    (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
    (hlegs : ∀ (ℓ : ℕ) [NeZero ℓ], (heckeAlphaC (IsLocalRing.ResidueField ↥A) L ℓ).toRingHom.IsIntegral ∧
      (heckeBetaC (IsLocalRing.ResidueField ↥A) L ℓ).toRingHom.IsIntegral) :
    letI := heckeModuleBar Lp
    ∃ (n : Nat.Primes → ℤ)
      (hcol : ∀ ℓ : Nat.Primes,
        HeckeRowSums (ssHeckeFamilyC p (IsLocalRing.ResidueField ↥A) L data hKr hlegs ℓ).transpose (n ℓ))
      (ε : ↥(toricMonodromyPart (J := JZero Lp) p (A.inertiaSubgroupIn ℚ)) ≃+
          (↥(characterLattice ↥(ssPlaces p L (IsLocalRing.ResidueField ↥A))) →+ Additive (IsLocalRing.ResidueField ↥A)ˣ)),
      (∀ (ℓ : Nat.Primes) (y : ↥(toricMonodromyPart (J := JZero Lp) p (A.inertiaSubgroupIn ℚ)))
        (x : ↥(characterLattice ↥(ssPlaces p L (IsLocalRing.ResidueField ↥A)))),
        ε (heckeGen ℓ • y) x =
          ε y (heckeCharacterAction (ssHeckeFamilyC p (IsLocalRing.ResidueField ↥A) L data hKr hlegs ℓ).transpose
            (hcol ℓ) x)) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ Lp → n ℓ = ((ℓ : ℕ) : ℤ) + 1) := by sorry
