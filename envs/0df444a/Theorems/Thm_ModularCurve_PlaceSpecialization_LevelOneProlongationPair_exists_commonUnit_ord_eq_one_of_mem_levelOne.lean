-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_commonUnit_ord_eq_one_of_mem_levelOne
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_commonUnit_ord_eq_one_of_mem_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/f47c3fd0-ede4-53a4-8a39-733804ead414
-- title:
--   Common unit with a simple zero at a prescribed place
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} \colon A \to k$; let `data` be modular polynomial data for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ in $Y$ annihilating the pair of $q$-expansions of $j$) satisfying the Kronecker congruence `hKr`, namely $\Phi \bmod q = (X^q - Y)(X - Y^q)$, and let `hα`, `hβ` assert that the two degeneracy inclusions $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ of the level-$1$ into the level-$q$ function field over $\overline{\mathbb Q}$ are integral. Let $P$ be a place specialisation for these data, sending places of `modularFunctionFieldBar (1 * q)` to places of `modularFunctionFieldC k 1` with the prescribed behaviour on $j$ and $j_q$ and with an induced map on degree-zero Picard groups, and write $\mathrm{red}_1$, $\mathrm{red}_2$ for the composites of $P.\mathrm{sp}$ with restriction along $\mathrm{heckeAlphaBar}$, resp. $\mathrm{heckeBetaBar}$. Let $R$ be a level-one prolongation pair for $P$: a lift $\overline{\mathrm{red}}$ of $\mathrm{red}$ to the residue field of $A$, an embedding $\iota$ of level-one function fields, and two regular prolongations $R_1$, $R_2$ of $A$ to `modularFunctionFieldBar (1 * q)` with residue field the level-one function field over the residue field of $A$, subject to the compatibilities that coefficientwise reductions of Laurent series lie in $R_1$ with the expected residue, that $R_2.\mathrm{integers}$ is the preimage of $R_1.\mathrm{integers}$ under the Fricke involution with $R_2$-residue the $R_1$-residue of the Fricke translate, and that $\iota \circ R_1.\mathrm{residue}$ agrees with the localised reduction map. Assume $R$ is a model (the two divisor laws and the two cusp laws), satisfies the order law at Frobenius-fixed places, the node value law `hval` for $\mathrm{red}$, and the regularity law relative to a finite set $S_0 \subseteq k$ whose members are exactly the $j$-invariants $j$ such that every elliptic curve over $k$ with $j$-invariant $j$ has no nonzero $q$-torsion point. Let $T$ be a finite set of places of `modularFunctionFieldC k 1`, none of which is supersingular (rational, affine geometric, with value of the geometric $j$-coordinate in that set of $j$-invariants), and let $V_0$ be a place of `modularFunctionFieldBar (1 * q)` with $\mathrm{red}_1 V_0 \in T$ or $\mathrm{red}_2 V_0 \in T$. Then there are a nonzero $f$ in `modularFunctionFieldBar (1 * q)` lying in $R_1.\mathrm{integers}$ and in $R_2.\mathrm{integers}$, with nonzero residues under $R_1.\mathrm{residue}$ and $R_2.\mathrm{residue}$, together with a divisor $D$ with $D(V) = \mathrm{ord}_V(f)$ at every place $V$, such that $D(V_0) = 1$; every $V \ne V_0$ in the support of $D$ satisfies $\mathrm{red}_1 V \notin T$ and $\mathrm{red}_2 V \notin T$; every $V \ne V_0$ with $D(V) > 0$ has $\mathrm{red}_1 V$ not supersingular; and the pair of orders of the level-one residues $R.\mathrm{residue}_1$ of $f$ at $\mathrm{red}_1 V_0$ and $R.\mathrm{residue}_2$ of $f$ at $\mathrm{red}_2 V_0$ is either $(1,0)$ or $(0,1)$.
--
--   This is the level-one one-point mover on $X_0(q)$ in characteristic $q$: it produces a function which is a unit for both prolongations of the valuation ring, has a simple zero at a prescribed place $V_0$ above the bad locus, keeps the rest of its divisor away from the finite set $T$ and from the supersingular fibres, and whose two reductions have orders $(1,0)$ or $(0,1)$ at the two reductions of $V_0$. It is used, via [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_pole_of_reduceFst_fixed_ordinary_levelOne_univ`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_pole_of_reduceFst_fixed_ordinary_levelOne_univ), to move divisor classes on the two components of the reduction of the modular curve into general position.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_commonUnit_ord_eq_one_of_mem_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_commonUnit_ord_eq_one_of_mem_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hval : LevelOneProlongationPair.NodeValueLaw q red)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k)
    (hNR : R.RegularityLaw S₀)
    (T : Finset (Place k ↥(modularFunctionFieldC k 1)))
    (hT : ∀ t ∈ T, t ∉ ssPlaces q 1 k)
    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hV₀ : P.redFst V₀ ∈ T ∨ P.redSnd V₀ ∈ T) :
    ∃ (f : ↥(modularFunctionFieldBar (1 * q))) (hf₁ : f ∈ R.R₁.integers) (hf₂ : f ∈ R.R₂.integers)
      (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      f ≠ 0 ∧ R.R₁.residue ⟨f, hf₁⟩ ≠ 0 ∧ R.R₂.residue ⟨f, hf₂⟩ ≠ 0 ∧
      (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧
      (∀ V ∈ D.support, V ≠ V₀ → P.redFst V ∉ T ∧ P.redSnd V ∉ T) ∧
      (∀ V, V ≠ V₀ → 0 < D V → P.redFst V ∉ ssPlaces q 1 k) ∧
      (((P.redFst V₀).ord (R.residue₁ ⟨f, hf₁⟩) = 1 ∧ (P.redSnd V₀).ord (R.residue₂ ⟨f, hf₂⟩) = 0) ∨
       ((P.redFst V₀).ord (R.residue₁ ⟨f, hf₁⟩) = 0 ∧ (P.redSnd V₀).ord (R.residue₂ ⟨f, hf₂⟩) = 1)) := by sorry
