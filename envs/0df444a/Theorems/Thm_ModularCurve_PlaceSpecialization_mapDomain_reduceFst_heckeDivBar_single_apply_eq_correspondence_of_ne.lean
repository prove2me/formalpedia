-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_mapDomain_reduceFst_heckeDivBar_single_apply_eq_correspondence_of_ne
-- name    : ModularCurve.PlaceSpecialization.mapDomain_reduceFst_heckeDivBar_single_apply_eq_correspondence_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/b03af112-c1ba-5ad8-8348-8fefa7a657e0
-- title:
--   First reduction of the Hecke divisor of one place
-- statement:
--   Fix $N$ with $N \neq 0$ and a prime $q$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, so that the residue field $\kappa =$ `ResidueField A` has characteristic $q$. Let `data` be a modular polynomial datum of level $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ killing the pair $(j_q, j_{q^q})$), let `hKr` assert the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q) \bmod q$, let $h\alpha, h\beta$ assert integrality of the two degeneracy legs $\alpha, \beta$ from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$, and let $P$ be a place specialisation of level $N$ at $A$ with reduction map `IsLocalRing.residue A`. Let $\ell$ be a prime with $\ell \neq q$, with integrality hypotheses for the legs from level $Nq$ to level $Nq\ell$ over $\overline{\mathbb{Q}}$ and for the legs $\beta_C, \alpha_C$ from `modularFunctionFieldC` $\kappa\,N$ into the characteristic-$q$ degeneracy roof `charLDegeneracyRoof` $\kappa\,N\,\ell$, principal divisors being available on the level-$Nq\ell$ function field over $\overline{\mathbb{Q}}$ and on that roof. Let $V$ be a place of `modularFunctionFieldBar (N * q)`, and assume that push-forward along $P.\mathrm{reduceFst}$ (restriction along the level-$Nq$ inclusion followed by $P.\mathrm{sp}$) intertwines `heckeDivBar`, the correspondence $\alpha_*\beta^*$ at level $Nq$, with `heckeDivFibre`, the correspondence $(\alpha_C)_*(\beta_C)^*$ at level $N$ over $\kappa$, on all divisors. Then: (i) for every place $s$ of `modularFunctionFieldC` $\kappa\,N$, the coefficient at $s$ of $(P.\mathrm{reduceFst})_*\,T_\ell[V]$ equals the coefficient at $s$ of $(\alpha_C)_*(\beta_C)^*\,[P.\mathrm{reduceFst}\,V]$; and (ii) if $P.\mathrm{reduceFst}\,V$ lies in `ssPlaces q N` $\kappa$ (rational, affine geometric, with $j$-value in the supersingular set for $q$), then every place in the support of $(P.\mathrm{reduceFst})_*\,T_\ell[V]$ lies in `ssPlaces q N` $\kappa$.
--
--   This is the single-place form of the compatibility of the Hecke correspondence $T_\ell$ ($\ell \neq q$) with reduction of $X_0(Nq)$ at $q$: the reduction of the $T_\ell$-divisor of a place is computed node by node by the fibre correspondence $(\alpha_C)_*(\beta_C)^*$ in characteristic $q$, and supersingularity of the reduced place propagates to the whole support. It is used in the computation of the Hecke action on the component group in the two `componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_…` results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_mapDomain_reduceFst_heckeDivBar_single_apply_eq_correspondence_of_ne.lean

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.mapDomain_reduceFst_heckeDivBar_single_apply_eq_correspondence_of_ne
    (N q : ℕ) [NeZero N] (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q →
          haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
          ∀ (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
            (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
            [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * ℓ))]
            [HasPrincipalDivisors (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ)]
            (hβc : HeckeBetaCIntegral (ResidueField A) N ℓ) (hαc : HeckeAlphaCIntegral (ResidueField A) N ℓ)
            (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
            (∀ X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
              Finsupp.mapDomain P.reduceFst (heckeDivBar hαℓ hβℓ X) =
                heckeDivFibre (ResidueField A) N ℓ hβc hαc (Finsupp.mapDomain P.reduceFst X)) →
            (∀ s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N),
              Finsupp.mapDomain P.reduceFst (heckeDivBar hαℓ hβℓ (Finsupp.single V (1 : ℤ))) s =
                Divisor.correspondence (heckeBetaC (ResidueField A) N ℓ) (heckeAlphaC (ResidueField A) N ℓ)
                  hβc hαc (Finsupp.single (P.reduceFst V) 1) s) ∧
            (P.reduceFst V ∈ ssPlaces q N (ResidueField A) →
              ∀ s ∈ (Finsupp.mapDomain P.reduceFst (heckeDivBar hαℓ hβℓ (Finsupp.single V (1 : ℤ)))).support,
                s ∈ ssPlaces q N (ResidueField A)) := by sorry
