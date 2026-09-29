-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw
-- name    : ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/a6745174-76ac-5ef8-bb64-ec5b9c93ada0
-- title:
--   Model prolongation tuple with regularity, node-value and order laws
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive integer $N$, and an algebraically closed field $k$ of characteristic $q$ together with a surjective ring homomorphism $red : A \to k$. Fix also $data$, a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the $q$-th modular polynomial relation, a proof $hKr$ that its reduction mod $q$ equals $(C X^q - X)(C X - X^q)$, and proofs $h\alpha$, $h\beta$ that the two Hecke maps $\overline{\alpha}$, $\overline{\beta}$ at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Assume the genus $genusFF$ of the modular function field $modularFunctionFieldC\ k\ N$ over $k$ — the $k$-dimension of $H^1$ of the zero divisor — is positive, that $q \nmid N$, and let $P$ be a place specialisation in the sense of `PlaceSpecialization` (a map of places from level $N$ over $\overline{\mathbb{Q}}$ to level $N$ over $k$, together with a homomorphism on degree-zero divisor classes and compatibility conditions for $j$, $j_N$ and their poles). Let $W$ be a finite set of places of $modularFunctionFieldC\ k\ N$ whose elements are exactly the supersingular places $ssPlaces\ q\ N\ k$. Then there exists a prolongation tuple $R$ over $P$ — a pair of regular prolongations $R_1$, $R_2$ of the level-$Nq$ function field over $\overline{\mathbb{Q}}$ to the level-$N$ function field over the residue field of $A$, linked by the Atkin–Lehner involution and by a reduction homomorphism $\iota$ down to $k$ — such that: $R$ is a model, i.e. it satisfies the two divisor laws and the two cusp laws at $\infty$ and at $0$; $R$ satisfies the regularity law for $W$, so that for $f$ in both integer rings whose orders at all places of level $Nq$ above an affine geometric place $v$ fixed by the square of the geometric Frobenius are non-negative, the two residues have non-negative order at $v$ and at its Frobenius translate respectively, and at each node pair of $W$ for the arithmetic Frobenius the two residues take a common value; $R$ satisfies the node-value law for $W$, i.e. that common value may be taken non-zero when both residues are non-zero and no place where $f$ has non-trivial order reduces to the given node pair; and $R$ satisfies the fixed-place order law, computing the pushforward along $P$'s first reduction of the divisor of such an $f$ at a Frobenius-square-fixed affine geometric place $v$ as $\operatorname{ord}_v$ of the first residue plus $\operatorname{ord}$ at the Frobenius translate of $v$ of the second residue.
--
--   This is the level-$N$ form of the existence of a semistable model of the modular curve of level $Nq$ in characteristic $q$, with its two components meeting at the supersingular points, packaged as the combined model, regularity, node-value and fixed-place order laws for a prolongation tuple attached to a prescribed place specialisation. It is the input to the two-level semistable specialisation statements of the Čerednik–Drinfeld part of the development and to the one-sided regularity law for models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    [DecidableEq k] (hg : 0 < genusFF k ↥(modularFunctionFieldC k N)) (hqN : ¬ q ∣ N)
    (hred : Function.Surjective red)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) :
    ∃ R : ProlongationTuple P, R.IsModel ∧ R.RegularityLaw W ∧ R.NodeValueLaw W ∧ R.OrderLawFixed := by sorry
