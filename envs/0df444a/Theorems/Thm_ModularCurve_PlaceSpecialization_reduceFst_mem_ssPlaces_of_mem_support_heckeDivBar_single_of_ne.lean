-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_mem_ssPlaces_of_mem_support_heckeDivBar_single_of_ne
-- name    : ModularCurve.PlaceSpecialization.reduceFst_mem_ssPlaces_of_mem_support_heckeDivBar_single_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/bcc3b7aa-ba65-5ae3-9085-f37a399f858f
-- title:
--   Supersingularity propagates along the ℓ-Hecke correspondence, ℓ ≠ q
-- statement:
--   Fix a nonzero natural number $N$ and a prime $q$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$, in the sense that $q$ is a non-unit of $A$; then the residue field $\kappa = \mathrm{ResidueField}\,A$ has characteristic $q$. Let `data` be a `ModularPolynomialData q`, that is a monic polynomial $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions, subject to the Kronecker congruence `hKr` asserting that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)\,(C(X) - X^q)$; let `hα`, `hβ` assert that the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of level $N$ and prime $q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms, and let $P$ be a `PlaceSpecialization` of these data at $A$ with residue map `IsLocalRing.residue A`, so in particular $P$ provides a map `P.sp` from places of $\overline{\mathbb Q}$-level-$N$ modular function field to places of the level-$N$ function field over $\kappa$, a homomorphism on $J_0$-classes, and the stated order-comparison clauses for $j$ and $j_N$. Let $\ell$ be a prime different from $q$, let `hαℓ`, `hβℓ` assert integrality of the two degeneracy maps of level $Nq$ and prime $\ell$ over $\overline{\mathbb Q}$, and assume that every nonzero element of the level-$Nq\ell$ function field over $\overline{\mathbb Q}$ has a divisor of degree $0$ recording its orders at all places. Then for all places $V, V'$ of the level-$Nq$ modular function field over $\overline{\mathbb Q}$: if $P.\mathrm{reduceFst}\,V$, the image under `P.sp` of the restriction of $V$ along the level-$N$ degeneracy map `heckeAlphaBar`, lies in `ssPlaces q N κ`, the set of places satisfying `IsSupersingularPlace q N`, and if $V'$ lies in the support of the divisor obtained by applying the Hecke correspondence `heckeDivBar hαℓ hβℓ` (pullback along `heckeAlphaBar` followed by pushforward along `heckeBetaBar`, for level $Nq$ and prime $\ell$) to the divisor $1\cdot[V]$, then $P.\mathrm{reduceFst}\,V'$ also lies in `ssPlaces q N κ`.
--
--   This is the statement that supersingularity of the first reduction is preserved by the Hecke correspondence $T_\ell$ at primes $\ell \ne q$: the $\ell$-neighbours of a place of $X_0(Nq)$ whose level-$N$ reduction along the first degeneracy map is supersingular again have supersingular first reduction, reflecting the classical fact that supersingularity is stable under isogeny of degree prime to the characteristic. It is used in the computation of the Hecke action on the component group at $q$, in the lemmas comparing `componentGroupProj` of a dualised depth with `heckeComponentAction`, and in the identification of the push-forward of `heckeDivBar` along `reduceFst` with a correspondence downstairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_reduceFst_mem_ssPlaces_of_mem_support_heckeDivBar_single_of_ne.lean

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_GlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.reduceFst_mem_ssPlaces_of_mem_support_heckeDivBar_single_of_ne
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
            [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * ℓ))],
          ∀ V V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
            P.reduceFst V ∈ ssPlaces q N (ResidueField A) →
            V' ∈ (heckeDivBar hαℓ hβℓ (Finsupp.single V (1 : ℤ))).support →
              P.reduceFst V' ∈ ssPlaces q N (ResidueField A) := by sorry
