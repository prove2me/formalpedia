-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_spData_mem_admissible
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.spData_mem_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/0cc88772-190e-5d65-96af-c829389af470
-- title:
--   Admissibility of the twisted gluing datum at level N
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, an algebraically closed perfect field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, a datum `data` of a modular polynomial for $q$ satisfying the Kronecker congruence `hKr`, integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings $\mathrm{modularFunctionFieldBar}\,N \to \mathrm{modularFunctionFieldBar}(Nq)$, a place specialisation $P$ for these data and a prolongation tuple $R$ for $P$. Assume $q \nmid N$, and let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$ whose members are exactly the supersingular places $\mathrm{ssPlaces}\,q\,N\,k$. Let `dat` be a level-$N$ annulus datum over $W$ for $R$ whose correction divisors satisfy, for every $w \in W$: $\mathrm{corrFst}\,w$ and $\mathrm{corrSnd}\,w$ vanish at every $v \in W$ and have degree $-1$. Let $a$ be a twist vector for $W$ and $D$ a divisor on $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$ satisfying the two branch equations $\deg (P.\mathrm{fstDiv}\,D) = -\sum_{w \in W} \mathrm{endOrderFst}\,a\,D\,w$ and $\deg (P.\mathrm{sndDiv}\,D) = -\sum_{w \in W} \mathrm{endOrderSnd}\,a\,D\,w$, where $\mathrm{fstDiv}$, $\mathrm{sndDiv}$ are the restrictions of $D$ to the places that are strict for the first, respectively second, branch. Then $\mathrm{spData}\,a\,D$ is admissible for the node pairs $\{(w, \mathrm{arithFrobC}\,q\,k\,N \cdot w) : w \in W\}$: the divisor $\mathrm{reduceFst}_{*}(P.\mathrm{fstDiv}\,D) - \sum_{w \in W} \mathrm{endOrderFst}\,a\,D\,w \cdot \mathrm{corrFst}\,w$ has degree zero and vanishes at each $w \in W$, and $\mathrm{reduceSnd}_{*}(P.\mathrm{sndDiv}\,D) - \sum_{w \in W} \mathrm{endOrderSnd}\,a\,D\,w \cdot \mathrm{corrSnd}\,w$ has degree zero and vanishes at each $\mathrm{arithFrobC}\,q\,k\,N \cdot w$ with $w \in W$; no condition is imposed on the unit component $\mathrm{nodeUnitOf}\,a\,D$.
--
--   This is the admissibility check for the gluing datum attached to a divisor on $X_0(Nq)$ in the Deligne–Rapoport description of the fibre at $q$ as two copies of $X_0(N)_{/\mathbb F_q}$ crossing at the supersingular points, the condition needed for the datum to define a class in the glued degree-zero Picard group. It is used in the construction of fixed strict divisors with good kernel behaviour from twist data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_spData_mem_admissible.lean

import Mathlib
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.spData_mem_admissible
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} {R : P.ProlongationTuple} (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (dat : R.AnnulusDatumLevel W)
    (hcorrFst : ∀ w ∈ W, (∀ v ∈ W, dat.corrFst w v = 0) ∧ Divisor.degree (dat.corrFst w) = -1)
    (hcorrSnd : ∀ w ∈ W, (∀ v ∈ W, dat.corrSnd w v = 0) ∧ Divisor.degree (dat.corrSnd w) = -1)
    (a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (ha₁ : Divisor.degree (P.fstDiv D) = -∑ w ∈ W, dat.endOrderFst a D w)
    (ha₂ : Divisor.degree (P.sndDiv D) = -∑ w ∈ W, dat.endOrderSnd a D w) :
    dat.spData a D ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) := by sorry
