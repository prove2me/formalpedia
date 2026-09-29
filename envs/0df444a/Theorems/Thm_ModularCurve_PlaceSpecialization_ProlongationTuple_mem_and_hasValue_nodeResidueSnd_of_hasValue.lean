-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_and_hasValue_nodeResidueSnd_of_hasValue
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.mem_and_hasValue_nodeResidueSnd_of_hasValue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/616f8ee2-9b56-57a6-a1d2-860da4428c8c
-- title:
--   Node-ring values reduce to the second residue at Frob· w
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero level $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix modular polynomial data `data` for $q$ together with a proof `hKr` that its bivariate reduction modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and proofs $h\alpha$, $h\beta$ that the two degeneracy maps $\overline{\mathcal F}_N \to \overline{\mathcal F}_{Nq}$ (inclusion, and the $q$-expansion twist) are integral. Let $P$ be a place specialisation of these data and $R$ a prolongation tuple over $P$, and assume principal divisors exist on $\overline{\mathcal F}_{Nq} =$ `modularFunctionFieldBar (N * q)` over $\overline{\mathbb Q}$. Assume `hord`, the order law of $R$ at the places fixed by the square of $\varphi =$ `frobOnPlacesGeomLevel k N data hKr`, and, for a finite set $W$ of places of `modularFunctionFieldC k N` all of which are supersingular (rational, affine, with $j$-value in the supersingular set `ssJSet q k`), the regularity law `R.RegularityLaw W`. Let $w \in W$ satisfy $\varphi(\varphi\, w) = w$, let $f \in \overline{\mathcal F}_{Nq}$ lie in the node ring `R.nodeIntegers w`, that is, $f$ is integral for $R_1$ and for $R_2$ and lies in the valuation ring of every place $V$ of $\overline{\mathcal F}_{Nq}$ over $\overline{\mathbb Q}$ with $P.\mathrm{reduceFst}\,V = w$, and let $V$ be such a place with $f$ taking the value $c \in \overline{\mathbb Q}$ at $V$ (that is, $f$ lies in the valuation ring of $V$ and its image in the residue field of $V$ is that of $c$). Then $c$ lies in $A$ and the element `R.nodeResidue₂ w ⟨f, hf⟩` of `modularFunctionFieldC k N` takes the value $\mathrm{red}(c)$ at the place `arithFrobC q k N • w`, the image of $w$ under the arithmetic Frobenius semilinear automorphism, which by [`ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel`](thm.html#ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel) is $\varphi\, w$.
--
--   This is the second-component half of the compatibility between values of members of the node ring at a characteristic-zero place above a supersingular node and values of their reductions on the two components of the special fibre, the first component being treated by the companion statement. It is used by the value–residue compatibility lemma [`ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_nodeResidueSnd_red_evalAt_of_orderLawFixed`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_nodeResidueSnd_red_evalAt_of_orderLawFixed) and by the two existence results for crossing presentations of the node ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_and_hasValue_nodeResidueSnd_of_hasValue.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.mem_and_hasValue_nodeResidueSnd_of_hasValue
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
    (hord : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ∈ R.nodeIntegers w)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w)
    (c : AlgebraicClosure ℚ) (hc : V.HasValue f c) :
    ∃ hcA : c ∈ A, (arithFrobC q k N • w).HasValue (R.nodeResidue₂ w ⟨f, hf⟩ : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩) := by sorry
