-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_and_hasValue_nodeResidueFst_of_hasValue
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.mem_and_hasValue_nodeResidueFst_of_hasValue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/b684cb8f-fe56-58d6-a2e5-1810fc182b3c
-- title:
--   Values of node-ring elements specialise to the first residue
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a natural number $N \neq 0$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality of the two degeneracy maps `heckeAlphaBar`, `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbb Q}$ (`hα`, `hβ`), a place specialisation $P$ for these choices, a prolongation tuple $R$ over $P$, and assume principal divisors exist on $\overline{\mathbb Q}(X_0(Nq)) =$ `modularFunctionFieldBar (N * q)`. Assume $R$ satisfies the fibre-sum order law `OrderLawFixed`, let $W$ be a finite set of places of `modularFunctionFieldC k N` each of which is supersingular (rational, affine as a geometric place, with $j$-value in `ssJSet q k`), and assume the regularity law `RegularityLaw W` for $R$. Let $w \in W$ be fixed by the square of the geometric-level Frobenius `frobOnPlacesGeomLevel k N data hKr`. Let $f$ lie in the node ring `R.nodeIntegers w`, i.e. $f$ lies in the valuation subrings `R.R₁.integers`, `R.R₂.integers` and in the valuation subring of every place $V$ of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb Q}$ with `P.reduceFst V = w` (the restriction of $V$ along `heckeAlphaBar`, pushed through `P.sp`). Let $V$ be such a place and $c \in \overline{\mathbb Q}$ with $f$ taking the value $c$ at $V$, meaning $f$ lies in the valuation subring of $V$ and reduces there to the image of $c$. The conclusion is that $c \in A$ and that the element `R.nodeResidue₁ w ⟨f, hf⟩` of `modularFunctionFieldC k N` takes the value $\mathrm{red}(c)$ at $w$.
--
--   This is the characteristic-zero locality of the node ring in value form: values, unlike orders, specialise from a place over a supersingular node to the first component of the special fibre. It is used by the lemmas producing crossing presentations of the node ring at supersingular points and by the non-unit criteria for differences $f -$ constant at such points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_and_hasValue_nodeResidueFst_of_hasValue.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.mem_and_hasValue_nodeResidueFst_of_hasValue
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
    ∃ hcA : c ∈ A, w.HasValue (R.nodeResidue₁ w ⟨f, hf⟩ : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩) := by sorry
