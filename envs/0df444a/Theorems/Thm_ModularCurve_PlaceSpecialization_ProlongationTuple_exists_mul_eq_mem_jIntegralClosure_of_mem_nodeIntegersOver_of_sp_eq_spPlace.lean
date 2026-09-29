-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_mem_jIntegralClosure_of_mem_nodeIntegersOver_of_sp_eq_spPlace
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mul_eq_mem_jIntegralClosure_of_mem_nodeIntegersOver_of_sp_eq_spPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/1f9bb695-625a-503f-b74b-acf62dc274b4
-- title:
--   Node integers are fractions with denominator a unit at the node
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a natural number $N \neq 0$, a field $k$ of characteristic $q$ which is algebraically closed, and a ring homomorphism $\mathrm{red} \colon A \to k$; fix modular polynomial data `data` at level $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing at $(j, j_q)$) satisfying the Kronecker congruence $\overline{\Phi} = (X^q - Y)(X - Y^q)$ in the reduction `reduceModBivar`, together with the integrality hypotheses $h\alpha, h\beta$ asserting that the Hecke homomorphisms `heckeAlphaBar`, `heckeBetaBar` at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral. Assume $q \nmid N$, let `fm` be a fibre model for $N$, $A$, $q$, $k$, $\mathrm{red}$, assume $\mathrm{red}$ surjective, let `dataAll` assign modular polynomial data to every divisor $d \mid N$, and let `hsep` assert that $\Phi$ at level $N$, reduced mod $q$ and viewed over $\mathrm{RatFunc}\,k$, is separable. Let $P$ be a place specialisation for these data whose underlying map on places satisfies $P.\mathrm{sp} =$ `fm.spPlace hred dataAll hsep`, let $R$ be a prolongation tuple over $P$ (carrying the two regular prolongations $R_1, R_2$ of $\overline{\mathbb{Q}}$-places of the level-$Nq$ modular function field with residues into the level-$N$ fibre field), and let $w$ be a place of $\mathrm{modularFunctionFieldC}\,k\,N$ lying in `ssPlaces q N k`, i.e. supersingular. The conclusion is an eventual statement in the base field: for every number field $K \subseteq \overline{\mathbb{Q}}$ there is a number field $K' \supseteq K$ such that for every number field $K'' \supseteq K'$ and every $g$ in the level-$Nq$ modular function field over $\overline{\mathbb{Q}}$ lying in $R.\mathrm{nodeIntegersOver}\,K''\,w$ — that is, $g$ is an $R_1$-integer and an $R_2$-integer, $g$ lies in the valuation subring of every $\overline{\mathbb{Q}}$-place $V$ with $P.\mathrm{reduceFst}\,V = w$, and its Laurent series lies in `fieldOver (N*q) K''` — there exist $c$ and $s$ in the same field with $s \in R.\mathrm{nodeIntegers}\,w$ such that the Laurent series of $c$ and of $s$ both lie in $\mathrm{jIntegralClosure}\,(Nq)\,A\,K''$ (elements of `fieldOver (N*q) K''` integral over $\mathrm{jRing}\,A\,K''$), the first residue $R.\mathrm{nodeResidue}_1\,w\,s$ does not have value $0$ at $w$, and $g \cdot s = c$.
--
--   This expresses the node ring at a supersingular point of the fibre of $X_0(Nq)$ at $q$ as a localisation of the normalisation: after enlarging the base number field, every element of the node ring is a fraction $c/s$ with numerator and denominator integral over $A_0[j]$ and with denominator a unit at the node. It is used to transport values of residues through such fractions and to prove that the ring of node integers over a sufficiently large number field is local and Noetherian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_mem_jIntegralClosure_of_mem_nodeIntegersOver_of_sp_eq_spPlace.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mul_eq_mem_jIntegralClosure_of_mem_nodeIntegersOver_of_sp_eq_spPlace
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
          ∀ g : ↥(modularFunctionFieldBar (N * q)), g ∈ R.nodeIntegersOver K'' w →
            ∃ (c s : ↥(modularFunctionFieldBar (N * q))) (hs : s ∈ R.nodeIntegers w),
              (c : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'' ∧
              (s : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'' ∧
              ¬ w.HasValue (R.nodeResidue₁ w ⟨s, hs⟩ : ↥(modularFunctionFieldC k N)) (0 : k) ∧
              g * s = c := by sorry
