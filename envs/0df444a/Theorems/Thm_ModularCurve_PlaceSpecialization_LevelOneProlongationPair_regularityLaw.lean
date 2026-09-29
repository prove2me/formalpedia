-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_regularityLaw
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.regularityLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/e4724441-48fa-55ce-859e-0771dc72a9c4
-- title:
--   Regularity law for level-one prolongation pairs of X₀(q)
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of an algebraic closure of $\mathbb{Q}$, let $k$ be an algebraically closed field of characteristic $q$, and let $\mathrm{red} \colon A \to k$ be a ring homomorphism. Let `data` be modular polynomial data for $q$, that is, a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions, and let `hKr` be the Kronecker congruence asserting that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$; let `hα`, `hβ` assert that the two Hecke correspondence homomorphisms $\overline{\alpha}, \overline{\beta}$ at level $1$ and prime $q$ over the algebraic closure of $\mathbb{Q}$ are integral ring homomorphisms. Let $P$ be a place specialisation `PlaceSpecialization A q 1 data hKr k red hα hβ`, and let $R$ be a level-one prolongation pair for $P$: a reduction $\overline{\mathrm{red}}$ of the residue field of $A$ to $k$ lifting $\mathrm{red}$, a coefficientwise embedding $\iota$ of the full level-one function field over the residue field of $A$ into `modularFunctionFieldC k 1`, and two regular prolongations $R_1, R_2$ of $A$ to the function field $\overline{F} =$ `modularFunctionFieldBar (1 * q)`, whose integral elements are exchanged by the Fricke involution ($f \in R_2$'s integers iff the Fricke involute of $f$ lies in $R_1$'s integers, with residues matching accordingly) and whose residues compute the localised characteristic-$q$ reduction of $\overline{F}$. Let $S_0$ be a finite subset of $k$ each of whose elements $a$ lies in `ssJSet q k`, that is, every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero affine point killed by $q$. Then $R$ satisfies `RegularityLaw S₀`: for every $f \in \overline{F}$ integral for both $R_1$ and $R_2$, writing $\varphi$ for `frobOnPlacesGeomLevel k 1 data hKr` and $\mathrm{res}_1 f$, $\mathrm{res}_2 f$ for the associated residues in `modularFunctionFieldC k 1`, (i) for every place $v$ of `modularFunctionFieldC k 1` over $k$ with $\varphi(\varphi(v)) = v$, with $v$ distinct from the image under $P$'s first reduction map of the cusp $\overline{\infty}$ of $\overline{F}$, and such that $\operatorname{ord}_W f \ge 0$ for every place $W$ of $\overline{F}$ reducing to $v$, one has $\operatorname{ord}_v(\mathrm{res}_1 f) \ge 0$ whenever $\mathrm{res}_1 f \neq 0$ and $\operatorname{ord}_{\varphi(v)}(\mathrm{res}_2 f) \ge 0$ whenever $\mathrm{res}_2 f \neq 0$; and (ii) for every $a \in S_0$ with $a^{q^2} = a$ such that $\operatorname{ord}_W f \ge 0$ for every place $W$ of $\overline{F}$ reducing to the first member of `frobNodePair q a`, there is a $c \in k$ at which $\mathrm{res}_1 f$ takes the value $c$ at the first member of `frobNodePair q a` and $\mathrm{res}_2 f$ takes the value $c$ at its second member (having a value $c$ at a place meaning that the element lies in the corresponding valuation subring and its residue is the image of $c$).
--
--   This is the statement that the reduction of a function of $\overline{F}$ integral along both Gauss valuations of the Kronecker model of $X_0(q)$, with no pole centred at a given Frobenius-square-fixed place, is regular there on both branches, and takes matching values on the two branches at a supersingular crossing; it thus discharges, for an arbitrary level-one prolongation pair, the regularity hypothesis used when reductions of bi-integral functions are assembled into sections on the glued special fibre. It is invoked by the level-one prolongation-tuple results on residues of functions with prescribed poles and by the computation of residues on the multiplicative covering chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_regularityLaw.lean

import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.regularityLaw
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    {S₀ : Finset k} (hS₀ : ∀ a ∈ S₀, a ∈ ssJSet q k) :
    R.RegularityLaw S₀ := by sorry
