-- Prove2me | Theorems.Thm_ModularCurve_isResiduallyModularOfLevel_of_hasLowerLevelTorsion_of_isGoodPrimeFor
-- name    : ModularCurve.isResiduallyModularOfLevel_of_hasLowerLevelTorsion_of_isGoodPrimeFor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/681cf52d-61b4-597c-a6fb-59ceaaef2859
-- title:
--   Residual modularity at level N from lower-level torsion
-- statement:
--   Let $p$ be a prime (as a `Fact` instance) and $W$ a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$. Assume: the $p$-torsion of the group of points of $W$ base-changed to $\mathbb{Q}$ and then to $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` has cardinality $p^2$; the resulting homomorphism from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to the $\mathbb{Z}/p$-linear endomorphisms of that torsion module factors through a finite level, i.e. there is a finite-dimensional intermediate field $L$ with $\mathbb{Q} \subseteq L \subseteq \overline{\mathbb{Q}}$ such that every automorphism fixing $L$ pointwise acts as the identity; `W.ModRepIsIrreducible p`, i.e. the $p$-torsion module is nontrivial and its only Galois-stable $\mathbb{Z}/p$-submodules are $\bot$ and $\top$. Let $q$ be a prime with $q \neq p$ such that the associated [`ResidualGaloisRep`](def/GaloisRep_Residual.html#L22) is unramified at $q$ (for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit in $A$, every element of the inertia subgroup of $A$ over $\mathbb{Q}$ acts as the identity) and $q \nmid \Delta_W$ (`W.IsGoodPrimeFor q`). Let $N$ be a nonzero natural number with $q \nmid N$, and assume the project's Hecke-side inputs at level $N$: `HeckeInputsAll N` (the integrality, principal-divisor, finiteness, fundamental-identity and norm-formula data for the two degeneracy maps at every prime) and `HeckeOperatorsCommuteBar N` (the operators `heckeOperatorBar N ℓ` on `JZero N`, the degree-zero divisor class group of the level-$N$ modular function field over $\overline{\mathbb{Q}}$, commute pairwise). Let $\mathfrak{m}$ be a maximal ideal of the polynomial Hecke algebra $\mathrm{HeckeAlg} = \mathbb{Z}[X_\ell : \ell \text{ prime}]$ with $p \in \mathfrak{m}$ and with $\mathrm{heckeGen}(\ell) - C(a_\ell(W)) \in \mathfrak{m}$ for every prime $\ell \nmid N q$ with $\ell \neq p$ and $\ell \nmid \Delta_W$, where $a_\ell(W)$ is the trace of Frobenius of the reduction of $W$ mod $\ell$. Finally let $S$ be a finite set of primes all dividing $Nq$, and assume `HasLowerLevelTorsion S 𝔪 (JZero N)` for the Hecke module structure `heckeModuleBar N`: there is a nonzero $y \in \mathrm{JZero}\,N$ killed by every natural number lying in $\mathfrak{m}$ and by every element $\mathrm{heckeGen}(\ell) - C(b) \in \mathfrak{m}$ with $\ell \notin S$ and $b \in \mathbb{Z}$. The conclusion is `W.IsResiduallyModularOfLevel p N`: there exist a weight-two cusp form $f$ for $\Gamma_0(N)$ satisfying the project's normalised-eigenform conditions (first $q$-coefficient $1$, multiplicativity at coprime indices, and the two prime-power recursions) and a maximal ideal $\mathfrak{M}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ with $p \in \mathfrak{M}$, such that for every prime $\ell \nmid \Delta_W$ with $\ell \nmid N$ and $\ell \neq p$ there is an algebraic integer $a$ with $a =$ the $\ell$-th $q$-coefficient of $f$ and $a - a_\ell(W) \in \mathfrak{M}$.
--
--   This is the level-lowering step in the shape used by Ribet and Mazur: a mod $p$ eigensystem congruent to $W$ that is realised by torsion in the Jacobian at level $N$ already comes from a normalised eigenform of level $N$, so that the congruence holds at all good primes away from $N$ and $p$, in particular at $q$. Unlike the textbook statement, the hypotheses here are packaged on the Hecke side: the congruence is encoded by membership of the elements $T_\ell - a_\ell(W)$ in a maximal ideal $\mathfrak{m}$ of an abstract polynomial Hecke algebra, and the geometric input is the existence of a nonzero element of $\mathrm{JZero}\,N$ annihilated by the integers in $\mathfrak{m}$ and by the relevant $T_\ell - b$ outside a finite set $S$ of primes dividing $Nq$. The result is used to remove one prime from a squarefree level, in [`WeierstrassCurve.isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf`](thm.html#WeierstrassCurve.isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf), which passes from residual modularity of level $M$ to level $M/q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isResiduallyModularOfLevel_of_hasLowerLevelTorsion_of_isGoodPrimeFor.lean

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_MazurPrincipleCore

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem ModularCurve.isResiduallyModularOfLevel_of_hasLowerLevelTorsion_of_isGoodPrimeFor
    (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (hirr : W.ModRepIsIrreducible p) (q : ℕ) (hq : q.Prime) (hqp : q ≠ p)
    (hunr : ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).IsUnramifiedAt q)
    (hqΔ : W.IsGoodPrimeFor q)
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    (hin : HeckeInputsAll N) (hcomm : HeckeOperatorsCommuteBar N)
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hpm : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (hcong : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N * q → ℓ ≠ p →
      heckeGen ⟨ℓ, hℓ⟩ - MvPolynomial.C (W.apOfModel ℓ : ℤ) ∈ 𝔪)
    (S : Finset Nat.Primes) (hS : ∀ ℓ ∈ S, (ℓ : ℕ) ∣ N * q)
    (hlow : letI := heckeModuleBar N; HasLowerLevelTorsion S 𝔪 (JZero N)) :
    W.IsResiduallyModularOfLevel p N := by sorry
