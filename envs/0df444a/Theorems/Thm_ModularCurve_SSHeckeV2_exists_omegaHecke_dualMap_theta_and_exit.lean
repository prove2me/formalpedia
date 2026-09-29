-- Prove2me | Theorems.Thm_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit
-- name    : ModularCurve.SSHeckeV2.exists_omegaHecke_dualMap_theta_and_exit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/2729eab5-27c5-5a5d-b9eb-38a1d1bbd6c0
-- title:
--   Dual Hecke operators on Ω(D') and the cuspidal exit
-- statement:
--   Let $p\ge 5$ be a prime, $K$ an algebraically closed field of characteristic $p$, $N$ a non-zero natural number, and $F=\mathrm{modularFunctionFieldC}\,K\,N$ the subfield of $K((q))$ generated over $K$ by $\bar\jmath=\mathrm{jqModC}\,K$ and its $N$-fold $q$-expansion; $F$ is assumed to be a curve over $K$ (principal divisors of degree zero, residue fields finite over $K$, $\Omega_{F/K}$ free of rank one), to admit canonical divisors, to have every place's local coordinate $\mathrm{dCoord}$ generating $\Omega_{F/K}$, to have $\Omega_{F/K}$ non-trivial and canonical local residue data, and `hagree` asserts `WeilKaehlerAgree`: for each non-zero $\omega$ the Weil functional $\lambda_\omega$ is non-zero, lies in $\Omega(\mathrm{canonicalDivisorOf}\,\omega)$, and $\mathrm{canonicalDivisorOf}\,\omega$ dominates every $D$ with $\lambda_\omega\in\Omega(D)$. Further hypotheses: at each place $w$ with $w(\bar\jmath)<0$ the integer $|w(\bar\jmath)|$ is non-zero in $K$; $N\neq 0$ in $K$; $1\le m$ and $2m\le p+1$; $SS$ a finset whose members are exactly the supersingular places; a divisor $D'$ equal to $\mathrm{weightDivisor}\,K\,N\,m$ away from the supersingular places of width dividing $m$ and to that divisor minus $1$ at those places; and a $K$-linear map $\Theta$ from $K$-valued functions on $\mathrm{SSIndex}\,p\,N\,K\,(2m)$ to the dual of $\mathrm{omegaSpace}\,D'$ whose value at $\lambda_\omega$, for $\omega\neq0$ with $\lambda_\omega\in\Omega(D')$, is $\sum_{x\in SS}\mathrm{kaehlerResidueTerm}\,\omega$ of the constant adele $\mathrm{liftFun}\,p\,N\,K\,(2m)\,v$ at $x$. Then there exist operators $T^\Omega_\ell\in\mathrm{End}_K\Omega(D')$ indexed by $\ell\in\mathbb N$, scalars $c_\ell\in K$ and an exponent $j\in\mathbb N$ such that: the $T^\Omega_\ell$ commute pairwise for primes $\ell,\ell'\nmid N$ with $\ell,\ell'\neq p$; $c_\ell\neq0$ for such $\ell$; $\Theta(\mathrm{ssHeckeFun}\,p\,N\,K\,(2m)\,\ell\,v)=c_\ell\cdot(T^\Omega_\ell)^{\mathrm t}(\Theta v)$ for all $v$; and for every set $S_0\ni p$ of naturals, every non-zero $\omega\in\Omega(D')$ and every family $\kappa$ with $T^\Omega_\ell\omega=\kappa_\ell\omega$ for all primes $\ell\nmid N$, $\ell\notin S_0$, there are $m'\ge1$ with $m+m'=(p+1)/2$ and a non-zero $G'\in F$ lying in $\mathrm{riemannRochSpace}(\mathrm{weightDivisor}\,K\,N\,m')$ whose Laurent series satisfies $\mathrm{IsModPCuspFormFn}\,K\,m'$ (namely $G'^6\bar\jmath^{4m'}(\bar\jmath-1728)^{3m'}$ is integral over $K[\bar\jmath]$, and $G'^{2M}\bar\jmath^{m'M+1}(\bar\jmath-1728)^{m'M}$ is integral over $K[\bar\jmath^{-1}]$ for some $M$), and which satisfies, for all primes $\ell\nmid N$ with $\ell\notin S_0$, the Hecke eigen-identity $\ell^{\,m'-1}\,\mathrm{Tr}\bigl(\mathrm{heckeBetaC}\,\ell\,G'\cdot\mathrm{heckeMultiplier}\,\ell^{\,m'}\bigr)=\ell^{\,j}(c_\ell\kappa_\ell)\,G'$, the trace being taken from $\mathrm{charLDegeneracyRoof}\,K\,N\,\ell$ down to $F$ along $\mathrm{heckeAlphaC}\,K\,N\,\ell$.
--
--   This is the differential side of the weight window: it produces Hecke operators on the space of Weil differentials bounded by $D'$ that are adjoint, up to non-zero scalars, to the supersingular Hecke operators under the residue pairing $\Theta$, together with the passage from a Hecke eigenvector of $\Omega(D')$ to a mod $p$ cusp form of the complementary weight $2m'$ with $m+m'=(p+1)/2$. It is used by [`ModularCurve.SSHeckeV2.ssHeckeFun_window`](thm.html#ModularCurve.SSHeckeV2.ssHeckeFun_window), the weight-window statement in the Serre-weight analysis underlying level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.lean

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.SSHeckeV2.exists_omegaHecke_dualMap_theta_and_exit
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    [AlgebraicCurve.IsCurveOver K ↥(modularFunctionFieldC K N)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := ↥(modularFunctionFieldC K N))]
    [∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates]
    [Nontrivial (Ω[↥(modularFunctionFieldC K N)⁄K])]
    [AlgebraicCurve.HasPrincipalDivisors K ↥(modularFunctionFieldC K N)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K ↥(modularFunctionFieldC K N)]
    (hagree : AlgebraicCurve.WeilKaehlerAgree K ↥(modularFunctionFieldC K N))
    (htame : ∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N),
      w.ord (jGeomGen K N) < 0 → (((w.ord (jGeomGen K N)).natAbs : ℕ) : K) ≠ 0)
    (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m) (hmp : 2 * m ≤ p + 1)
    (SS : Finset (AlgebraicCurve.Place K ↥(modularFunctionFieldC K N))) (hSS : ∀ x, x ∈ SS ↔ x ∈ ssPlaces p N K)
    (D' : AlgebraicCurve.Divisor K ↥(modularFunctionFieldC K N))
    (hD'1 : ∀ w, w ∈ ssPlaces p N K → ((placeWidth N w : ℤ) ∣ (m : ℤ)) → D' w = ModularCurve.weightDivisor K N m w - 1)
    (hD'0 : ∀ w, ¬ (w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) → D' w = ModularCurve.weightDivisor K N m w)
    (Θ : ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)) →ₗ[K]
        Module.Dual K ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D'))
    (hΘres : ∀ v (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) (hω : ω ≠ 0)
          (hmem : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω ∈
            AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D'),
          Θ v ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩
            = ∑ x ∈ SS, kaehlerResidueTerm ω
                (diagonalHom K ↥(modularFunctionFieldC K N) (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v)) x) :
    ∃ (TΩ : ℕ → Module.End K ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D')) (c : ℕ → K) (j : ℕ),
      (∀ ℓ ℓ', ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p → ℓ'.Prime → ¬ ℓ' ∣ N → ℓ' ≠ p → Commute (TΩ ℓ) (TΩ ℓ')) ∧
      (∀ ℓ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p → c ℓ ≠ 0) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ≠ p → ∀ v,
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          Θ (ModularCurve.ssHeckeFun p N K hp5 (2 * (m : ℤ)) ℓ v) = c ℓ • (TΩ ℓ).dualMap (Θ v)) ∧
      (∀ (S₀ : Set ℕ) (_ : p ∈ S₀) (ω : ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D')) (κ : ℕ → K), ω ≠ 0 →
          (∀ ℓ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → TΩ ℓ ω = κ ℓ • ω) →
          ∃ (m' : ℕ) (hm' : 1 ≤ m') (_ : m + m' = (p + 1) / 2) (G' : ↥(modularFunctionFieldC K N)),
            G' ≠ 0 ∧ G' ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m') ∧
            ModularCurve.IsModPCuspFormFn K m' (G' : LaurentSeries K) ∧
            ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
              haveI : Fact ℓ.Prime := ⟨hℓ⟩
              letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
              algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m' - 1)) *
                  Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
                    (heckeBetaC K N ℓ G' * ModularCurve.heckeMultiplier N K ℓ ^ m')
                = algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ j * (c ℓ * κ ℓ)) * G') := by sorry
