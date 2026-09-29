-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_matrix_eq_correspondence_gluedSpecialization_nodeUnit_heckeGen_of_ne_of_isModel_of_prolongation_of_regularityLaw_nodeValueLaw
-- name    : ModularCurve.PlaceSpecialization.exists_matrix_eq_correspondence_gluedSpecialization_nodeUnit_heckeGen_of_ne_of_isModel_of_prolongation_of_regularityLaw_nodeValueLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/bbe7ac6d-0caf-5d20-8d72-492ef5e0cddd
-- title:
--   T_ℓ (ℓ≠ q) acts on node units by a correspondence matrix
-- statement:
--   Let $N\ge 1$ and let $q$ be a prime with $q\nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, so that $\kappa:=\mathrm{ResidueField}\,A$ has characteristic $q$; the groups $\mathrm{JZero}(Nq)=\mathrm{Pic}^0$ of `modularFunctionFieldBar (N*q)` and $\mathrm{JZero}(N)$ carry their `heckeModuleBar` module structures over $\mathrm{HeckeAlg}=\mathbb Z[X_\ell]$. Fix a finite set $W$ of places of `modularFunctionFieldC` $\kappa$ $N$ consisting exactly of the supersingular places `ssPlaces q N κ`, write $g=$ `arithFrobC q κ N` and $S=\{(w,g\cdot w):w\in W\}$, and assume $S$ is node-stable, i.e. $(g\cdot s_1,g\cdot s_2)\in S$ for all $s\in S$. Further data: a `ModularPolynomialData q` satisfying the Kronecker congruence, integrality of the two degeneracy embeddings at level $(N,q)$ in characteristic zero, a place-specialisation datum $P$ for $A$, $q$, $N$ with reduction `residue A`, a prolongation tuple $R$ for $P$ which is a model (the two divisor laws and the two cusp laws) and satisfies the regularity law and node-value law for $W$ and the fixed-place order law, a regular prolongation $R_1$ of $A$ from `modularFunctionFieldBar N` to `modularFunctionFieldC κ N` whose residue transports divisors along $P.\mathrm{sp}$ (for $f$ in $R_1$'s integers with non-zero residue, the pushforward along $P.\mathrm{sp}$ of the divisor of $f$ has at each place $Q$ the value $Q.\mathrm{ord}$ of the residue of $f$), a width function $e$ on places, and additive maps $\mathrm{comp}$ from the inertia invariants $H=\mathrm{inertiaInvariants}\,A\,(Nq)\subseteq \mathrm{JZero}(Nq)$ onto the component group of the width datum $s\mapsto e(s_1)$ on $S$ and $\mathrm{sp}:H\to \mathrm{GluedPic0}\,\kappa\,(\mathrm{modularFunctionFieldC}\,\kappa\,N)\,S$, with $\mathrm{comp}$ surjective, $\mathrm{comp}\,x=0$ if and only if $x$ is a good class for $P$ relative to $S$, and $\mathrm{sp}$ a glued specialisation for $P$. Then for every prime $\ell\ne q$, given integrality of the degeneracy maps `heckeAlphaBar`, `heckeBetaBar` at level $(N,\ell)$ and of `heckeAlphaC`, `heckeBetaC` over $\kappa$, existence of principal divisors on the relevant function fields, the assumption that every place of `charLDegeneracyRoof κ N ℓ` has degree $1$, a regular prolongation $R_\ell$ of $A$ from `modularFunctionFieldBar (N*ℓ)` to that roof together with a map $r_\ell$ on places transporting divisors as above, compatibility of $R_\ell$'s residue with $R_1$'s along `heckeAlphaBar`/`heckeAlphaC` and along `heckeBetaBar`/`heckeBetaC`, and equality of the degrees of the pullbacks of a single place $v$ and of $P.\mathrm{sp}(v)$ along the two pairs of degeneracy maps, there exist an integer matrix $T$ indexed by $S\times S$ and $n\in\mathbb Z$ such that: for each index the sum of $T$ over its first index equals $n$; $n$ is the degree `finrankAlong κ (heckeAlphaC κ N ℓ)`; $T_{s t}$ is the coefficient at $s_1$ of the divisor correspondence (pullback along `heckeAlphaC` followed by pushforward along `heckeBetaC`) applied to the single place $t_1$; and for every $x\in H$ with $X_\ell\cdot x\in H$ and $\mathrm{comp}\,x=0$, and every $w:S\to \mathrm{Additive}\,\kappa^\times$ with $\mathrm{sp}\,x$ the node unit of $w$, the element $\mathrm{sp}(X_\ell\cdot x)$ is the node unit of $t\mapsto \sum_s T_{s t}\cdot w_s$.
--
--   This is the statement that on the torus part of the inertia invariants of $J_0(Nq)$ at $q$ — the node-unit part of the glued Picard group of the two copies of $X_0(N)_\kappa$ crossing at the supersingular points — the Hecke operator $T_\ell$ for $\ell\ne q$ acts through the integral matrix of the Hecke correspondence on the supersingular nodes, whose column sums are constant and equal to the degree of the first degeneracy map. It feeds the variant [`ModularCurve.PlaceSpecialization.exists_matrix_eq_correspondence_gluedSpecialization_nodeUnit_heckeGen_of_ne_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_matrix_eq_correspondence_gluedSpecialization_nodeUnit_heckeGen_of_ne_of_isModel), in which part of the auxiliary data is discharged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_matrix_eq_correspondence_gluedSpecialization_nodeUnit_heckeGen_of_ne_of_isModel_of_prolongation_of_regularityLaw_nodeValueLaw.lean

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
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_matrix_eq_correspondence_gluedSpecialization_nodeUnit_heckeGen_of_ne_of_isModel_of_prolongation_of_regularityLaw_nodeValueLaw (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
      (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
      (R₁ : RegularProlongation A (modularFunctionFieldBar N) (modularFunctionFieldC (ResidueField A) N))
      (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          (∀ V, D V = V.ord (f : modularFunctionFieldBar N)) →
        ∀ Q, Finsupp.mapDomain P.sp D Q = Q.ord (R₁.residue f))
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (hsurj : Function.Surjective comp)
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp),
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
                  (Finsupp.single (P.sp v) 1))),
          ∃ T : Matrix ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
              ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ℤ, ∃ n : ℤ,
            (∀ s, ∑ t, T t s = n) ∧
            n = (finrankAlong (ResidueField A) (heckeAlphaC (ResidueField A) N ℓ) : ℤ) ∧
            (∀ s t : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W),
              T s t = Divisor.correspondence (heckeAlphaC (ResidueField A) N ℓ)
                (heckeBetaC (ResidueField A) N ℓ) hαc hβc (Finsupp.single t.1.1 1) s.1.1) ∧
            ∀ (x : ↥(inertiaInvariants A (N * q)))
              (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
              comp x = 0 →
                ∀ w : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) →
                    Additive (ResidueField A)ˣ,
                  sp x = GluedPic0.nodeUnit
                      (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) w →
                    sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩ =
                      GluedPic0.nodeUnit (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                        (fun t => ∑ s, T s t • w s) := by sorry
