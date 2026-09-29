-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidue_red_of_hasValue_of_mem_nodeIntegersOver_of_sp_eq_spPlace
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_nodeResidue_red_of_hasValue_of_mem_nodeIntegersOver_of_sp_eq_spPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/db014f65-7b8b-5410-a691-606fb4371b30
-- title:
--   Value bridge at a supersingular node over number fields
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive integer $N$, and an algebraically closed field $k$ of characteristic $q$ together with a surjective ring homomorphism $\mathrm{red}\colon A \to k$; assume $q \nmid N$. Let `data` be modular polynomial data in level $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) satisfying the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q) \bmod q$, and let $h\alpha$, $h\beta$ assert that the Hecke correspondence maps $\overline{\alpha}$, $\overline{\beta}$ for $(N,q)$ are integral. Let `fm` be a fibre model for $N$ over $A$ with reduction $\mathrm{red}$, let `dataAll` assign modular polynomial data to each divisor of $N$, and let `hsep` say that $\Phi$ in level $N$, reduced mod $q$ and viewed over $\mathrm{RatFunc}(k)$, is separable. Let $P$ be a place specialisation for these data whose underlying map $P.\mathrm{sp}$ on places is the one produced by `fm` from $(\mathrm{hred}, \mathrm{dataAll}, \mathrm{hsep})$, let $R$ be a prolongation tuple over $P$ (a pair of regular prolongations $R_1, R_2$ of $\overline{M}_{Nq}$ with values in the level-$N$ fibre field over the residue field of $A$, together with the coefficientwise identifications and the Atkin–Lehner dictionary between them), and let $w$ be a place of $\mathrm{modularFunctionFieldC}\ k\ N$ lying in $\mathrm{ssPlaces}\ q\ N\ k$, i.e. supersingular in the sense of `IsSupersingularPlace`. Then for every number field $K \subseteq \overline{\mathbb{Q}}$ there is a number field $K' \supseteq K$ such that for every number field $K'' \supseteq K'$, every place $V$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb{Q}}$ with $P.\mathrm{reduceFst}\,V = w$ (the specialisation under $P.\mathrm{sp}$ of the restriction of $V$ along $\overline{\alpha}$ equals $w$), every $g$ in the subring $R.\mathrm{nodeIntegersOver}\ K''\ w$ of elements of $R.\mathrm{nodeIntegers}\ w$ whose Laurent expansion lies in $\mathrm{NodeLocalized.fieldOver}(Nq)\,K''$, and every $c \in \overline{\mathbb{Q}}$ such that $g$ lies in the valuation subring of $V$ with residue the image of $c$, one has $c \in A$, and moreover $R.\mathrm{nodeResidue}_1\,w\,g$ has value $\mathrm{red}(c)$ at $w$ while $R.\mathrm{nodeResidue}_2\,w\,g$ has value $\mathrm{red}(c)$ at the place $\mathrm{arithFrobC}\ q\ k\ N \cdot w$ obtained by transporting $w$ along the coefficientwise Frobenius semilinear automorphism of the level-$N$ fibre field.
--
--   This is the compatibility between values in characteristic zero and values on the two branches through a supersingular node of the fibre of $X_0(Nq)$ at $q$, restricted to those members of the node ring whose $q$-expansion already has coefficients in a number field, and stated in the eventual form 'for all sufficiently large number fields'. It is the arithmetic input for the unrestricted version of the statement and, through it, for the identification of the local rings at the nodes (local, Noetherian, with the expected completion) used in the analysis of $X_0(Nq)$ in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidue_red_of_hasValue_of_mem_nodeIntegersOver_of_sp_eq_spPlace.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_nodeResidue_red_of_hasValue_of_mem_nodeIntegersOver_of_sp_eq_spPlace
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
          ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
            ∀ (g : ↥(R.nodeIntegersOver K'' w)) (c : AlgebraicClosure ℚ),
              V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
              ∃ hcA : c ∈ A,
                w.HasValue (R.nodeResidue₁ w ⟨g, g.2.1⟩ : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩) ∧
                (arithFrobC q k N • w).HasValue (R.nodeResidue₂ w ⟨g, g.2.1⟩ : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩) := by sorry
