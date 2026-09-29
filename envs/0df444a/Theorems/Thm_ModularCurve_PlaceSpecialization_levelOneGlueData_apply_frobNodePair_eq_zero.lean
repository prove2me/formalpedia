-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_levelOneGlueData_apply_frobNodePair_eq_zero
-- name    : ModularCurve.PlaceSpecialization.levelOneGlueData_apply_frobNodePair_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/a607067a-90ca-5cf0-9bbb-69e8cc8b264a
-- title:
--   Level-one gluing datum vanishes at supersingular node places
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb Q}$, and $k$ an algebraically closed field of characteristic $q$ equipped with a ring homomorphism $\mathrm{red} : A \to k$. Fix $data : \mathtt{ModularPolynomialData}\ q$, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions, together with a proof `hKr` that its reduction modulo $q$ equals $(C X^q - X)(C X - X^q)$, and proofs `hα`, `hβ` that the two degeneracy inclusions of the level-$1$ into the level-$q$ modular function field over $\overline{\mathbb Q}$ are integral. Let $P$ be a place specialisation of this data, $S_0$ a finite subset of $k$ each of whose elements $j$ has the property that every elliptic Weierstrass curve over $k$ with invariant $j$ has trivial $q$-torsion, and $D$ a divisor on the level-$1\cdot q$ modular function field over $\overline{\mathbb Q}$. Then for $a \in S_0$ the first component of the level-one gluing datum $P.\mathtt{levelOneGlueData}$ attached to $D$ and to the gluing set of pairs $(\tilde\jmath = b,\ \tilde\jmath = b^q)$, $b \in S_0$ — namely the pushforward along `P.redFst` of the `P.fstPart` of $D$ — vanishes at the place $\tilde\jmath = a$, and its second component, the pushforward along `P.redSnd` of the `P.sndPart` of $D$, vanishes at the place $\tilde\jmath = a^q$.
--
--   This is the node-avoidance half of the admissibility of the level-one gluing datum: the places attached to supersingular $j$-invariants, along which the two copies of the $j$-line are glued, carry no multiplicity from the reduced divisor. It is used in the construction of admissible representatives of classes in the glued Picard group, in [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_goodRep_admissible_smul_single_sub_self_of_eq_zero_or_eq`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_goodRep_admissible_smul_single_sub_self_of_eq_zero_or_eq) and its companion for the case of distinct non-zero values.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_levelOneGlueData_apply_frobNodePair_eq_zero.lean

import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.levelOneGlueData_apply_frobNodePair_eq_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (S₀ : Finset k) (hS₀ : ∀ a ∈ S₀, a ∈ ssJSet q k)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (a : k) (ha : a ∈ S₀) :
    (P.levelOneGlueData (nodePairsOf q S₀) D).1 (frobNodePair q a).1 = 0 ∧
      (P.levelOneGlueData (nodePairsOf q S₀) D).2.1 (frobNodePair q a).2 = 0 := by sorry
