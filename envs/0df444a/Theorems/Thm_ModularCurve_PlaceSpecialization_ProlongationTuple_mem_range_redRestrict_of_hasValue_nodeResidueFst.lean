-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/df2ab495-9654-5bd8-bfbc-e010573c39fb
-- title:
--   Node residue values at supersingular places are K-rational
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N \geq 1$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$, together with modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr` (the reduction of $\Phi$ modulo $q$ equals $(X^q - Y)(X - Y^q)$ in the bivariate sense), integrality hypotheses `hα`, `hβ` for the Hecke maps $\bar\alpha$, $\bar\beta$ at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$, a place specialisation $P$ of this data and a prolongation tuple $R$ over $P$. Assume $q \nmid N$, let $K$ be a subfield of $\overline{\mathbb{Q}}$ finite over $\mathbb{Q}$, and let $w$ be a place of the modular function field $\mathrm{modularFunctionFieldC}\,k\,N = k(\tilde\jmath, \tilde\jmath_N)$ which is supersingular for $q$ and $N$ (that is, $w \in$ `ssPlaces q N k`). Assume moreover that every $a' \in k$ with $a'^{q^2} = a'$ lies in the image of `NodeLocalized.redRestrict red K`, the restriction of $\mathrm{red}$ along the inclusion of `coeffSubring A K` into $A$. Let $g$ belong to the subring `R.nodeIntegersOver K w` of $\mathrm{modularFunctionFieldBar}(Nq)$, consisting of the elements of `R.nodeIntegers w` whose underlying Laurent series lies in `NodeLocalized.fieldOver (N * q) K`, and let $a \in k$ be a value of the first residue `R.nodeResidue₁ w` of $g$ at $w$, in the sense that this element of $k(\tilde\jmath, \tilde\jmath_N)$ lies in the valuation subring of $w$ and its residue is the image of $a$ in the residue field of $w$. Then $a$ lies in the image of `NodeLocalized.redRestrict red K`.
--
--   This is the descent step in the proof that the residue maps of the node ring of $X_0(Nq)$ at a supersingular crossing are surjective: a function defined over the number field $K$ takes, at a supersingular point, a value that is the reduction of a constant of $A \cap K$, reflecting the $\mathbb{F}_{q^2}$-rationality of supersingular points. It is invoked by the lemmas producing uniformisers and comparing the values of the two residues of the node ring at such a place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (g : ↥(R.nodeIntegersOver K w)) (a : k)
    (ha : w.HasValue (R.nodeResidue₁ w ⟨g, g.2.1⟩ : ↥(modularFunctionFieldC k N)) a) :
    a ∈ Set.range (NodeLocalized.redRestrict red K) := by sorry
