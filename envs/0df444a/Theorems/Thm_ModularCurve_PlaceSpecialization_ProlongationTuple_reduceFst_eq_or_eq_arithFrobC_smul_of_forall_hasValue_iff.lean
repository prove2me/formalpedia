-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceFst_eq_or_eq_arithFrobC_smul_of_forall_hasValue_iff
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.reduceFst_eq_or_eq_arithFrobC_smul_of_forall_hasValue_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/26bc9ab5-b72b-5c01-a16b-2fe74bd20dfc
-- title:
--   Value dictionary forces reduction to w or its Frobenius translate
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero level $N$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$, together with data $\mathrm{data}$ for the modular polynomial at $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing on the pair $(j, j_q)$), a proof `hKr` that $\Phi$ reduces mod $q$ to $(X^q - Y)(X - Y^q)$ in the bivariate sense of `KroneckerCongruence`, and proofs $h\alpha$, $h\beta$ that the two Hecke degeneracy maps $\overline{\alpha}$, $\overline{\beta}$ from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Let $P$ be a place specialization of these data, $R$ a prolongation tuple over $P$ (with its two regular prolongations $R_1$, $R_2$ of the level-$Nq$ function field), and assume $k$ algebraically closed and $q \nmid N$. Let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ (no finiteness over $\mathbb{Q}$ is assumed), let $w$ be a place of $\mathrm{modularFunctionFieldC}\ k\ N$ lying in `ssPlaces q N k`, i.e. satisfying `IsSupersingularPlace q N k`, and suppose $R$ satisfies `OrderLawFixed`: for every $f$ integral for both $R_1$ and $R_2$ with both residues nonzero, and every divisor $D$ of $f$, the pushforward of $D$ along `P.reduceFst` at any affine geometric place fixed by the square of the geometric Frobenius is the sum of the orders of the two residues at that place and at its Frobenius image. Let finally $W$ be a place of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb{Q}}$ satisfying the following dictionary hypothesis: for every element $t$ of $\mathrm{modularFunctionFieldBar}(Nq)$ whose Laurent series lies in the ring `jIntegralClosure (N * q) A K`, that is, lies in $\mathrm{fieldOver}(Nq)\,K$ and is integral over the ring $\mathrm{jRing}\ A\ K$, there is $a \in A$ with $W$ taking the value $a$ at $t$ (so $t$ lies in the valuation subring of $W$ and its residue is the image of $a$), such that $a$ lies in the maximal ideal of $A$ if and only if $t$ is $R_1$-integral and the residue $R.\mathrm{residue}_1(t)$, an element of $\mathrm{modularFunctionFieldC}\ k\ N$, takes the value $0$ at $w$. Then `P.reduceFst W`, the image under $P.\mathrm{sp}$ of the restriction of $W$ along $\overline{\alpha}$, equals either $w$ or $\mathrm{arithFrobC}\ q\ k\ N \cdot w$, the translate of $w$ by the semilinear automorphism of $\mathrm{modularFunctionFieldC}\ k\ N$ induced by the Frobenius $x \mapsto x^q$ on coefficients.
--
--   This identifies, up to the ambiguity of the arithmetic $q$-Frobenius, the reduction along the first degeneracy map of a characteristic-zero place of the level-$Nq$ function field whose values on the $K$-rational normal $j$-model are prescribed by a fixed supersingular place $w$ of the level-$N$ curve in characteristic $q$; the ambiguity is unavoidable because supersingular places are fixed only by the square of Frobenius. It is used in the construction of maximal ideals of the rings of node integers over $K$, in the analysis of the regularity law for the two branches of the reduction of $X_0(Nq)$ at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceFst_eq_or_eq_arithFrobC_smul_of_forall_hasValue_iff.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization
set_option synthInstance.maxHeartbeats 400000 in

theorem
ModularCurve.PlaceSpecialization.ProlongationTuple.reduceFst_eq_or_eq_arithFrobC_smul_of_forall_hasValue_iff
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) (hO : R.OrderLawFixed)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hdict : ∀ (t : ↥(modularFunctionFieldBar (N * q)))
        (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
        ∃ a : A, W.HasValue t (a : AlgebraicClosure ℚ) ∧
          ((∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) ↔
            a ∈ IsLocalRing.maximalIdeal A)) :
    P.reduceFst W = w ∨ P.reduceFst W = arithFrobC q k N • w := by sorry
