-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residuePair_mem_riemannRochSpace_of_isGoodDivisor_or_eq_cuspInftyBar
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residuePair_mem_riemannRochSpace_of_isGoodDivisor_or_eq_cuspInftyBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/47815e87-a575-5bf0-8da3-10093ebf9ae3
-- title:
--   Residue pair of a Riemann–Roch section with cuspidal support
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$, and a ring homomorphism $\mathrm{red} : A \to k$; let `data` be modular polynomial data for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing on the pair of $q$-expansions) with `hKr` the Kronecker congruence $\Phi \equiv (Y^{q}-X)(Y-X^{q}) \bmod q$, and let $h\alpha$, $h\beta$ assert integrality of the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of the level-one field into $\bar F_{1\cdot q} =$ `modularFunctionFieldBar (1 * q)`. Let $P$ be a place specialization of $\bar F_{1\cdot q}$ along $A$, $\mathrm{red}$, and let $R$ be a level-one prolongation pair over $P$, with valuation subrings $R_1, R_2 \subseteq \bar F_{1\cdot q}$, residue maps to the level-one fibre field over the residue field of $A$, and comparison map $\iota$ into `modularFunctionFieldC k 1`; assume `R.IsModel`, i.e. the two divisor laws and the two cusp laws at $\infty$ and $0$. Let $S_0$ be a finite subset of $k$ whose members are exactly the elements of `ssJSet q k` (those $j$ such that every elliptic Weierstrass curve over $k$ with $j$-invariant $j$ has no nonzero $q$-torsion point), and assume the regularity law `R.RegularityLaw S₀`. Let $D$ be a divisor of $\bar F_{1\cdot q}/\overline{\mathbb{Q}}$ with $D(W) \ge 0$ for every place $W$, each place in the support of $D$ being strict of the first kind for $P$ (geometric Frobenius carries $\mathrm{red}_1 W$ to $\mathrm{red}_2 W$ and fixes no $\mathrm{red}_1 W$ after two steps), strict of the second kind (the symmetric condition with $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ and $\mathrm{Frob}^2(\mathrm{red}_2 W) \neq \mathrm{red}_2 W$), or the cusp `cuspInftyBar (1 * q)`. Finally let $G \in \bar F_{1\cdot q}$ lie in the Riemann–Roch space of $D$ (its adic valuation at each place $v$ is at most $\exp(D(v))$) and lie in both $R_1$ and $R_2$. Then: $\iota$ of the first residue of $G$ lies in the Riemann–Roch space of the pushforward along $\mathrm{red}_1$ of the strict first part of $D$ together with the multiplicity $D(\overline{\infty})$ placed at $\overline{\infty}$; $\iota$ of the second residue of $G$ lies in the Riemann–Roch space of the pushforward along $\mathrm{red}_2$ of the strict second part of $D$; and for every $a \in S_0$ there is $c \in k$ such that the place of `modularFunctionFieldC k 1` attached to the point $\tilde j = a$ takes the value $c$ on $\iota$ of the first residue and the place attached to $\tilde j = a^{q}$ takes the same value $c$ on $\iota$ of the second residue.
--
--   This is the transfer of Riemann–Roch data from the characteristic-zero modular curve of level $q$ to the two level-one branches of its reduction at $q$, together with the matching condition at the supersingular nodes where the branches cross; it is the version in which the cusp $\overline{\infty}$ is allowed in the support of $D$, its multiplicity being charged entirely to the first branch. It feeds the analysis of the expansion of residues along the $\infty$-chart in [`ModularCurve.MultCovering.infChart_residue_eq_ssPolyBar_mul_of_orthogonal`](thm.html#ModularCurve.MultCovering.infChart_residue_eq_ssPolyBar_mul_of_orthogonal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residuePair_mem_riemannRochSpace_of_isGoodDivisor_or_eq_cuspInftyBar.lean

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

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residuePair_mem_riemannRochSpace_of_isGoodDivisor_or_eq_cuspInftyBar
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair) (hR : R.IsModel)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) (hNR : R.RegularityLaw S₀)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hD : ∀ W, 0 ≤ D W) (hgood : ∀ W ∈ D.support,
      P.IsStrictTypeOne W ∨ P.IsStrictTypeTwo W ∨ W = cuspInftyBar (1 * q))
    (G : modularFunctionFieldBar (1 * q)) (hG : G ∈ riemannRochSpace D)
    (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers) :
    (R.ι (R.R₁.residue ⟨G, h₁⟩) : modularFunctionFieldC k 1) ∈
        riemannRochSpace (Finsupp.mapDomain P.redFst
          (P.fstPart D + Finsupp.single (cuspInftyBar (1 * q)) (D (cuspInftyBar (1 * q))))) ∧
    (R.ι (R.R₂.residue ⟨G, h₂⟩) : modularFunctionFieldC k 1) ∈
        riemannRochSpace (Finsupp.mapDomain P.redSnd (P.sndPart D)) ∧
    ∀ a ∈ S₀, ∃ c : k,
      (frobNodePair q a).1.HasValue (R.ι (R.R₁.residue ⟨G, h₁⟩) : modularFunctionFieldC k 1) c ∧
      (frobNodePair q a).2.HasValue (R.ι (R.R₂.residue ⟨G, h₂⟩) : modularFunctionFieldC k 1) c := by sorry
