-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residue_red_of_mem_jIntegralClosure_of_sp_eq_spPlace
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_residue_red_of_mem_jIntegralClosure_of_sp_eq_spPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/2231f626-093f-52e7-a0d1-8639407688e2
-- title:
--   Value bridge at a supersingular node for j-integral elements
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N\ge 1$ with $q\nmid N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$ which is assumed surjective; fix further modular polynomial data `data` for $q$ (a monic $\Phi\in\mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$ of $q$-expansions) satisfying the Kronecker congruence $hKr$, namely that the bivariate reduction of $\Phi$ equals $(C(X)^q-X)(C(X)-X^q)$, integrality hypotheses $h\alpha$, $h\beta$ for the two Hecke embeddings `heckeAlphaBar`, `heckeBetaBar` of level $N$ and prime $q$, a fibre model `fm` of type `CharPModel.FibreModel N A q k red`, modular polynomial data `dataAll` for every divisor of $N$, and the hypothesis `hsep` that the level-$N$ polynomial $\Phi_N$, reduced modulo $q$ and viewed over $k(T)$, is separable. Let $P$ be a place specialisation of type `PlaceSpecialization A q N data hKr k red hα hβ` whose underlying map on places agrees with the map `fm.spPlace hred dataAll hsep` attached to the fibre model, let $R$ be a prolongation tuple over $P$, with its two regular prolongations $R_1,R_2$ and associated residue maps into the characteristic-$q$ modular function field $\mathrm{modularFunctionFieldC}\ k\ N$, and let $w$ be a place of that field over $k$ lying in `ssPlaces q N k`, i.e. satisfying `IsSupersingularPlace q N k w`. The assertion is then: for every subfield $K\subseteq\overline{\mathbb{Q}}$ finite over $\mathbb{Q}$ there is a subfield $K'$ finite over $\mathbb{Q}$ with $K\le K'$ such that for every subfield $K''$ finite over $\mathbb{Q}$ with $K'\le K''$, every $t$ in the level-$Nq$ field $\mathrm{modularFunctionFieldBar}(Nq)$ whose underlying Laurent series lies in `jIntegralClosure (N*q) A K''` (that is, lies in `fieldOver (N*q) K''` and is integral over the ring `jRing A K''`), and every place $V$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb{Q}}$ with $P.\mathrm{reduceFst}\,V=w$ (the specialisation under $P$ of the restriction of $V$ along `heckeAlphaBar` is $w$), there exist $c\in A$ and proofs that $t$ lies in the integers of $R_1$ and in the integers of $R_2$, such that $t$ has value $c$ at $V$, the first residue `R.residue₁` of $t$ has value $\mathrm{red}(c)$ at $w$, and the second residue `R.residue₂` of $t$ has value $\mathrm{red}(c)$ at the translate $\mathrm{arithFrobC}\,q\,k\,N\cdot w$ of $w$ by the coefficientwise arithmetic Frobenius; here '$g$ has value $a$ at a place' means that $g$ lies in the valuation subring of the place and its image in the residue field is the image of $a$.
--
--   This is the compatibility, at a supersingular node of the special fibre at $q$, between the value of an element integral over $A_0[j]$ at a characteristic-zero place $V$ and the values of its two residues on the two components of the reduction of level $Nq$, the second taken at the Frobenius translate of $w$. It is the form of the bridge for elements with no denominators, and it feeds the node-residue statement [`ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_nodeResidue_red_of_hasValue_of_mem_nodeIntegersOver_of_sp_eq_spPlace`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_nodeResidue_red_of_hasValue_of_mem_nodeIntegersOver_of_sp_eq_spPlace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residue_red_of_mem_jIntegralClosure_of_sp_eq_spPlace.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_SpecializationMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_residue_red_of_mem_jIntegralClosure_of_sp_eq_spPlace
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (fm : CharPModel.FibreModel N A q k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hP : P.sp = fm.spPlace hred dataAll hsep)
    (R : ProlongationTuple P)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) :
    ∀ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K →
      ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K'), K ≤ K' ∧
        ∀ (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ K'' → K' ≤ K'' →
          ∀ t : ↥(modularFunctionFieldBar (N * q)),
            (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'' →
            ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
              ∃ (c : A) (h₁ : t ∈ R.R₁.integers) (h₂ : t ∈ R.R₂.integers),
                V.HasValue t (c : AlgebraicClosure ℚ) ∧
                w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (red c) ∧
                (arithFrobC q k N • w).HasValue (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N)) (red c) := by sorry
