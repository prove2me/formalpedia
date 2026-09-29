-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne
-- name    : ModularCurve.PlaceSpecialization.mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/6b024a28-c30d-545d-ab0e-ce29a8e82593
-- title:
--   First reduction at q commutes with T_ℓ, ℓ ≠ q
-- statement:
--   Let $N \geq 1$ and let $q$ be a prime; let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, so that its residue field $\kappa = \mathrm{ResidueField}(A)$ has characteristic $q$. Fix modular polynomial data at $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions of $j$) satisfying the Kronecker congruence $\Phi \equiv (C X^{q} - X)(C X - X^{q})$ modulo $q$, integrality hypotheses `hα`, `hβ` for the two degeneracy substitutions at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$, and a place specialisation $P$ of these data with respect to the residue map $A \to \kappa$, whose component `P.sp` sends places of $\mathrm{modularFunctionFieldBar}\,N$ to places of $\mathrm{modularFunctionFieldC}\,\kappa\,N$. Let $R_1$ be a regular prolongation of $A$ on $\mathrm{modularFunctionFieldBar}\,N$ with residue field map onto $\mathrm{modularFunctionFieldC}\,\kappa\,N$, and assume (`hr₁`) that for every $f$ in its valuation subring with non-zero residue, and every divisor $D$ whose coefficients are the orders of $f$, the pushforward $\mathrm{mapDomain}\,P.\mathrm{sp}\,D$ has, at each place $Q$, coefficient the order of $R_1.\mathrm{residue}\,f$ at $Q$. Let $\ell$ be a prime with $\ell \neq q$. Assume: integrality of the two degeneracy substitutions at level $N$ and prime $\ell$ over $\overline{\mathbb{Q}}$ and over $\kappa$; existence of principal divisors for $\mathrm{modularFunctionFieldBar}\,N$, $\mathrm{modularFunctionFieldBar}(N\ell)$ and the characteristic-$q$ degeneracy roof $\mathrm{charLDegeneracyRoof}\,\kappa\,N\,\ell$; that every place of that roof has degree $1$ over $\kappa$; a regular prolongation $R_\ell$ of $A$ on $\mathrm{modularFunctionFieldBar}(N\ell)$ with residues in the roof, together with a map $r_\ell$ of places satisfying the same divisor compatibility (`hrℓ`) as `hr₁`; that $R_\ell$'s residue map carries $\mathrm{heckeAlphaBar}$ and $\mathrm{heckeBetaBar}$ at level $N$, prime $\ell$, to $\mathrm{heckeAlphaC}$ and $\mathrm{heckeBetaC}$ applied to $R_1$'s residue; and that for each place $v$ the degree of the pullback of the single place $v$ along $\mathrm{heckeAlphaBar}$ (respectively $\mathrm{heckeBetaBar}$) equals the degree of the pullback of the single place $P.\mathrm{sp}\,v$ along $\mathrm{heckeAlphaC}$ (respectively $\mathrm{heckeBetaC}$). Assume further integrality of the two degeneracy substitutions at level $Nq$ and prime $\ell$ over $\overline{\mathbb{Q}}$, and existence of principal divisors for $\mathrm{modularFunctionFieldBar}(Nq\ell)$. Then for every divisor $X$ on $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb{Q}}$, the pushforward along $P.\mathrm{reduceFst}$ (restriction of a place along the level-$N$ degeneracy inclusion at $q$, followed by `P.sp`) of $\mathrm{heckeDivBar}$ applied to $X$ equals $\mathrm{heckeDivFibre}\,\kappa\,N\,\ell$ applied to the pushforward of $X$ along $P.\mathrm{reduceFst}$; here both Hecke operators are the correspondences given by pullback along the $\beta$-substitution followed by pushforward along the $\alpha$-substitution, at level $Nq$ upstairs and at level $N$ over $\kappa$ downstairs.
--
--   This is the commutation of the Hecke correspondence $T_\ell$, for $\ell$ distinct from the residue characteristic $q$, with specialisation of divisors onto the first component of the special fibre of $X_0(Nq)$ at $q$, in the divisor-theoretic form used for level lowering. It feeds the variant of the same statement formulated for a model with fixed order law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R₁ : RegularProlongation A (modularFunctionFieldBar N) (modularFunctionFieldC (ResidueField A) N))
      (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          (∀ V, D V = V.ord (f : modularFunctionFieldBar N)) →
        ∀ Q, Finsupp.mapDomain P.sp D Q = Q.ord (R₁.residue f)),
        ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q →
          ∀ [Fact (ℓ : ℕ).Prime]
            (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
            (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
            (hαc : HeckeAlphaCIntegral (ResidueField A) N ℓ)
            (hβc : HeckeBetaCIntegral (ResidueField A) N ℓ)
            [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N)]
            [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * (ℓ : ℕ)))]
            [HasPrincipalDivisors (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ)]
            (hdeg1 : ∀ Y : Place (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ), Y.deg = 1)
            (Rℓ : RegularProlongation A (modularFunctionFieldBar (N * (ℓ : ℕ)))
              (charLDegeneracyRoof (ResidueField A) N ℓ))
            (rℓ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * (ℓ : ℕ)))
              → Place (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ))
            (hrℓ : ∀ f : Rℓ.integers, Rℓ.residue f ≠ 0 →
              ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * (ℓ : ℕ))),
                (∀ V, D V = V.ord (f : modularFunctionFieldBar (N * (ℓ : ℕ)))) →
              ∀ Q, Finsupp.mapDomain rℓ D Q = Q.ord (Rℓ.residue f))
            (hRα : ∀ f : R₁.integers,
              ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N ℓ (f : modularFunctionFieldBar N) ∈ Rℓ.integers,
                Rℓ.residue ⟨_, h⟩ = heckeAlphaC (ResidueField A) N ℓ (R₁.residue f))
            (hRβ : ∀ f : R₁.integers,
              ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N ℓ (f : modularFunctionFieldBar N) ∈ Rℓ.integers,
                Rℓ.residue ⟨_, h⟩ = heckeBetaC (ResidueField A) N ℓ (R₁.residue f))
            (hdegα : ∀ v, Divisor.degree
                (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ (Finsupp.single v 1))
              = Divisor.degree (Divisor.pullbackAlong (heckeAlphaC (ResidueField A) N ℓ) hαc
                  (Finsupp.single (P.sp v) 1)))
            (hdegβ : ∀ v, Divisor.degree
                (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ (Finsupp.single v 1))
              = Divisor.degree (Divisor.pullbackAlong (heckeBetaC (ResidueField A) N ℓ) hβc
                  (Finsupp.single (P.sp v) 1)))
          (hαq : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
          (hβq : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q * (ℓ : ℕ)))]
          (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
          Finsupp.mapDomain P.reduceFst (heckeDivBar hαq hβq X) =
            heckeDivFibre (ResidueField A) N ℓ hβc hαc (Finsupp.mapDomain P.reduceFst X) := by sorry
