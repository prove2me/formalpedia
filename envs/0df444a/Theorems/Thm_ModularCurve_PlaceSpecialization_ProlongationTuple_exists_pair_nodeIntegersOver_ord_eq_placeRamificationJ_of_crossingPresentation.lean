-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_pair_nodeIntegersOver_ord_eq_placeRamificationJ_of_crossingPresentation
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_pair_nodeIntegersOver_ord_eq_placeRamificationJ_of_crossingPresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/55f74ebf-ec94-5b9d-8552-7780e905012e
-- title:
--   Branch-adapted pair from a level-q crossing presentation
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive level $N$, a field $k$ of characteristic $q$ that is algebraically closed, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality of the two Hecke maps at level $N$ and $q$, a place specialisation $P$ for these data and a prolongation tuple $R$ of $P$. Assume $q \nmid N$, let $W$ be a finite set of places of `modularFunctionFieldC k N` each of which is supersingular (rational, with $j$ and $j_N$ in its valuation subring, and $j$-value in `ssJSet q k`), assume `R.RegularityLaw W`, let $K \subseteq \overline{\mathbb Q}$ be a number field, let $w \in W$ with `w.evalAt (jGeomGen k N)` $= a$, and let $\varpi \in A \cap K$ generate the kernel of the reduction `redRestrict red K` in the sense that an element of $A \cap K$ reduces to $0$ exactly when it is a multiple of $\varpi$. Work in the subring `modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)` of $\mathrm{Laurent}(\overline{\mathbb Q})$, consisting of series $f$ with $f \cdot \Phi(s) = \Phi(r)$ for polynomials $r, s$ in two variables over $A \cap K$ whose specialisation $\Phi$ sends $X_0, X_1$ to the $q$-expansions $j$, $j_q$, with $s$ not vanishing at $(a, a^q)$ after reduction. Suppose given $G', H'$ in this subring, a natural number $E_1$, a unit $w_1$ of it with $G'H' = \varpi^{E_1} w_1$, and the ideal identities $(\varpi, G') = (\varpi, j_q - j^q)$ and $(\varpi, H') = (\varpi, j - j_q^{\,q})$, all brackets taken in that subring. The conclusion asserts the existence of $x', y', u'$ in `R.nodeIntegersOver K w` — the elements of `modularFunctionFieldBar (N * q)` lying in the integers of both $R.R_1$ and $R.R_2$, in the valuation subring of every place of `modularFunctionFieldBar (N * q)` whose first reduction under $P$ is $w$, and whose Laurent expansion lies in `NodeLocalized.fieldOver (N * q) K` — with $u'$ a unit, $x'y' = (\mathtt{R.nodeConst K w } \varpi)^{E_1} u'$, and, for the two residue maps `R.nodeResidue₁ w`, `R.nodeResidue₂ w` at the node (with values in `modularFunctionFieldC k N`): the first residue of $x'$ and the second residue of $y'$ vanish; the second residue of $x'$ is non-zero and has order at the place `arithFrobC q k N • w` equal to `placeRamificationJ N w`, the order of vanishing of $j - a$ at $w$; and the first residue of $y'$ is non-zero of order `placeRamificationJ N w` at $w$ itself.
--
--   This transports a crossing presentation of the local ring of the level-$q$ plane model at a supersingular point $(a, a^q)$ of its special fibre into the node ring at the corresponding place $w$ of level $N$, producing a pair of functions each vanishing on one of the two branches, with branch orders equal to the ramification index of $w$ over the $j$-line. It is used in the computation identifying the crossing exponent with a multiple of the width at $w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_pair_nodeIntegersOver_ord_eq_placeRamificationJ_of_crossingPresentation.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_PlaceWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_pair_nodeIntegersOver_ord_eq_placeRamificationJ_of_crossingPresentation
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ d : ↥(coeffSubring A K), redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (G' H' : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (E₁ : ℕ) (w₁ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hw₁ : IsUnit w₁)
    (hGH : G' * H' =
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ E₁ * w₁)
    (hGspan : Ideal.span {
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} = Ideal.span {
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))})
    (hHspan : Ideal.span {
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} = Ideal.span {
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}) :
    ∃ x' y' u' : ↥(R.nodeIntegersOver K w), IsUnit u' ∧ x' * y' = R.nodeConst K w ϖ ^ E₁ * u' ∧
      R.nodeResidue₁ w ⟨x', x'.2.1⟩ = 0 ∧ R.nodeResidue₂ w ⟨y', y'.2.1⟩ = 0 ∧
      R.nodeResidue₂ w ⟨x', x'.2.1⟩ ≠ 0 ∧
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨x', x'.2.1⟩) = (placeRamificationJ N w : ℤ) ∧
      R.nodeResidue₁ w ⟨y', y'.2.1⟩ ≠ 0 ∧
      w.ord (R.nodeResidue₁ w ⟨y', y'.2.1⟩) = (placeRamificationJ N w : ℤ) := by sorry
