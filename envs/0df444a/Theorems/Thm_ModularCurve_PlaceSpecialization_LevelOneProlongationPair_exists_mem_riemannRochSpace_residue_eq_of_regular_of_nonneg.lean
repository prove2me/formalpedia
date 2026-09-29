-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_riemannRochSpace_residue_eq_of_regular_of_nonneg
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_residue_eq_of_regular_of_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/ba5bf0e6-5053-5158-bcf7-ba610ee26d4a
-- title:
--   Lifting node-compatible level-one pairs into L(D)
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix data `data` for the modular polynomial at $q$ satisfying the Kronecker congruence `hKr`, integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings of the level-$1$ field into the level-$1\cdot q$ field, and a place specialization $P$ of $\overline{\mathbb Q}$-places of $\mathrm{modularFunctionFieldBar}\,1$ to $k$-places of $\mathrm{modularFunctionFieldC}\,k\,1$. Let $R$ be a level-one prolongation pair for $P$, consisting of a reduction $\mathrm{redBar}$ of the residue field of $A$ into $k$ compatible with $\mathrm{red}$, the induced coefficientwise map $\iota$ on level-one function fields, and two regular prolongations $R_1, R_2$ of $A$ to $\mathrm{modularFunctionFieldBar}\,(1\cdot q)$ with residue field $\mathrm{modularFunctionFieldFullC}(\mathrm{ResidueField}\,A)\,1$, whose residues are linked by the Fricke involution and which compute the characteristic-$q$ localized reduction. Assume $R$ satisfies `IsModel` (the two divisor laws and the two cusp laws), `OrderLawFixed`, the node value law `NodeValueLaw q red`, and the regularity law `RegularityLaw` for a finite set $S_0 \subseteq k$ whose elements are exactly the supersingular $j$-invariants in $k$, that is those $j$ for which every elliptic curve over $k$ with invariant $j$ has no nonzero $q$-torsion point. Let $D$ be a divisor on $\mathrm{modularFunctionFieldBar}\,(1\cdot q)$ with $D(W) \ge 0$ for every place $W$, good for $P$ (every place in the support is of strict type one or of strict type two), and with $2g \le \deg D + 1$ where $g$ is the genus $\mathrm{genusFF}$ of that field. Let $g_1, g_2$ lie in $\mathrm{modularFunctionFieldFullC}(\mathrm{ResidueField}\,A)\,1$ with $\iota g_1$ in the Riemann–Roch space of the pushforward along $P.\mathrm{redFst}$ of the strict-type-one part of $D$, with $\iota g_2$ in the Riemann–Roch space of the pushforward along $P.\mathrm{redSnd}$ of the strict-type-two part of $D$, and node-compatible: for each $a \in S_0$ there is $c \in k$ such that $\iota g_1$ takes the value $c$ at the place of $\mathrm{modularFunctionFieldC}\,k\,1$ attached to the point $a$ and $\iota g_2$ takes the same value $c$ at the place attached to $a^q$. Then there exists $G$ in $\mathrm{modularFunctionFieldBar}\,(1\cdot q)$ belonging to the integers of both $R_1$ and $R_2$, lying in the Riemann–Roch space of $D$, with $R_1$-residue $g_1$ and $R_2$-residue $g_2$.
--
--   This is the surjectivity half of the Deuring–Lamprecht comparison for the reduction of the function field of $X_0(q)$ at $q$ along the two Gauss prolongations: a pair of level-one functions on the two components of the special fibre, with matching values at the supersingular crossings and poles bounded by the two parts of a non-special effective good divisor $D$, is the residue pair of a single function in $L(D)$. It is used to produce functions whose divisor is controlled at the special fibre, in the results on common units of the two prolongations having order one at a prescribed place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_riemannRochSpace_residue_eq_of_regular_of_nonneg.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_residue_eq_of_regular_of_nonneg
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hval : LevelOneProlongationPair.NodeValueLaw q red)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) (hNR : R.RegularityLaw S₀)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hD : ∀ W, 0 ≤ D W) (hgood : P.IsGoodDivisor D)
    (hdeg : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) : ℤ) ≤ D.degree + 1)
    (g₁ g₂ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)
    (hg₁ : (R.ι g₁ : modularFunctionFieldC k 1) ∈
      riemannRochSpace (Finsupp.mapDomain P.redFst (P.fstPart D)))
    (hg₂ : (R.ι g₂ : modularFunctionFieldC k 1) ∈
      riemannRochSpace (Finsupp.mapDomain P.redSnd (P.sndPart D)))
    (hnode : ∀ a ∈ S₀, ∃ c : k,
      (frobNodePair q a).1.HasValue (R.ι g₁ : modularFunctionFieldC k 1) c ∧
      (frobNodePair q a).2.HasValue (R.ι g₂ : modularFunctionFieldC k 1) c) :
    ∃ (G : modularFunctionFieldBar (1 * q)) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      G ∈ riemannRochSpace D ∧ R.R₁.residue ⟨G, h₁⟩ = g₁ ∧ R.R₂.residue ⟨G, h₂⟩ = g₂ := by sorry
