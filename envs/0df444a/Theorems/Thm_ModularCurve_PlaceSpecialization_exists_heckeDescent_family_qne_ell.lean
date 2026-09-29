-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_heckeDescent_family_qne_ell
-- name    : ModularCurve.PlaceSpecialization.exists_heckeDescent_family_qne_ell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/fa4c69a5-fe6d-5f21-ba5d-ee276599f1f1
-- title:
--   Hecke descent family away from ℓ on the special fibre
-- statement:
--   Let $N\ge 1$ and assume `HeckeOperatorsCommuteBar N`, i.e. the operators $\bar T_q$ and $\bar T_{q'}$ on $J_0(N)=\mathrm{Pic}^0_{\overline{\mathbb Q}}(\bar F_N)$ commute for all primes $q,q'$. Let $\ell$ be a prime with $\ell\nmid N$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $\ell$ in the sense that $\ell$ is a non-unit of $A$, and let $\kappa_A$ be its residue field, assumed algebraically closed of characteristic $\ell$. Let `data` be a modular polynomial datum at $\ell$, that is a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(\ell)$ with $\Phi(j,j_\ell)=0$, satisfying the Kronecker congruence $\Phi\bmod\ell=(X^\ell-Y)(X-Y^\ell)$, and assume the two integrality conditions `HeckeAlphaBarIntegral` and `HeckeBetaBarIntegral` for $(\overline{\mathbb Q},N,\ell)$. Assume further that $\kappa_A$ together with the function field $\mathrm{modularFunctionFieldC}\,\kappa_A\,N$ satisfies `IsCurveOver` (principal divisors, places with finite residue extensions, and $\Omega$ free of rank one). Then for every place-specialization packet $S$ for $A$, $\ell$, $N$, the datum, and the reduction map $A\to\kappa_A$, there exists a family $T'_q$, indexed by the primes, of $\mathbb Z$-linear endomorphisms of $\mathrm{Pic}^0_{\kappa_A}(\mathrm{modularFunctionFieldC}\,\kappa_A\,N)$ such that $T'_q(S.\mathrm{spPic0}\,x)=S.\mathrm{spPic0}(\bar T_q x)$ for every prime $q\ne\ell$ and every $x\in J_0(N)$ (the action being that of `heckeModuleBar N`), and such that $T'_\ell$ is the $\mathbb Z$-linear map underlying `heckeFibreGeomLevelPic0OfIsCurveOver`. No intertwining property is asserted at $q=\ell$.
--
--   This is the descent of the Hecke operators $\bar T_q$, $q\ne\ell$, from $J_0(N)$ in characteristic zero through a place-specialization packet to the Jacobian of the special fibre at $\ell$, with the $\ell$-th member of the family fixed to be the geometric divisorial Hecke correspondence on the fibre. It is used in the construction of the Hecke-equivariant specialization packets that feed the Eichler–Shimura comparison at the prime $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_heckeDescent_family_qne_ell.lean

import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ValuationSubring AlgebraicCurve IsLocalRing
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem ModularCurve.PlaceSpecialization.exists_heckeDescent_family_qne_ell
    (N : ℕ) [NeZero N] (hcomm : HeckeOperatorsCommuteBar N)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    [IsCurveOver (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)]
    (S : PlaceSpecialization A ℓ N data hKr (ResidueField ↥A)
        (IsLocalRing.residue ↥A) hα hβ) :
    letI := heckeModuleBar N
    ∃ T' : Nat.Primes → Module.End ℤ
        (Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)),
      (∀ (q : Nat.Primes), (q : ℕ) ≠ ℓ → ∀ (x : JZero N),
          T' q (S.spPic0 x) = S.spPic0 (heckeGen q • x))
      ∧ T' ⟨ℓ, hℓ.out⟩
          = (heckeFibreGeomLevelPic0OfIsCurveOver
              (ResidueField ↥A) N data hKr).toIntLinearMap := by sorry
