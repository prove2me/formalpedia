-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_tubeEquation_smul_sub_self_of_annulus
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_tubeEquation_smul_sub_self_of_annulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/7ef88329-6c2f-5021-b9af-2dbfb95c93fe
-- title:
--   Tube equation for an inertial displacement on an annulus
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a level $N\ge 1$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$, together with modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality hypotheses $h\alpha,h\beta$ for the two degeneracy embeddings of level-$N$ into level-$Nq$ modular function fields over $\overline{\mathbb Q}$, a place specialisation $P$ for these data, and a prolongation tuple $R$ over $P$, whose two regular prolongations $R_1,R_2$ of $A$ to $F=\mathrm{modularFunctionFieldBar}\,(Nq)$ have residue maps `R.residue₁`, `R.residue₂` into the level-$N$ function field over $k$. Assume $\mathrm{red}\,c=0$ exactly for $c$ in the maximal ideal $\mathfrak m_A$; let $\sigma$ be a $\mathbb Q$-automorphism of $\overline{\mathbb Q}$ lying in the inertia subgroup of $A$ (the image of `A.inertiaSubgroup ℚ` in the automorphism group), $w$ a place of the level-$N$ function field over $k$, and $\mathcal A$ an annulus for $A$ in $F$, with domain `An.dom`, parameter $Z=$`An.param` and modulus $\pi=$`An.modulus` $\in\mathfrak m_A$. Assume: the domain of $\mathcal A$ consists exactly of the places $V'$ of $F$ with $P.\mathrm{reduceFst}\,V'=w$ for which neither $P.\mathrm{IsStrictFst}\,V'$ nor $P.\mathrm{IsStrictSnd}\,V'$ holds (i.e. neither does the geometric Frobenius on level-$N$ places carry the first reduction of $V'$ to its second reduction with its square moving the first reduction, nor does it carry the second reduction to the first with its square moving the second); $\pi\neq 0$ in $\overline{\mathbb Q}$; the semilinear automorphism `arithmeticGalois` attached to $\sigma$ fixes $Z$; $\pi^{-1}Z$ lies in the valuation subring $R_1.\mathrm{integers}$; $Z$ lies in $R_2.\mathrm{integers}$ with $\mathrm{res}_2(Z)\neq 0$. Then for every place $V$ in the domain of $\mathcal A$ there exist $x\in A$, a unit $u\in A^\times$ and $t\in F$ integral for both $R_1$ and $R_2$ such that $x\in\mathfrak m_A$, $\pi=xd$ for some $d\in\mathfrak m_A$, $\sigma(x)=ux$, $Z$ lies in the valuation ring of $V$ with residue the image of $x$, $t=(Z-\sigma(x))(Z-x)^{-1}$, $\mathrm{res}_1(t)$ is the image of $\mathrm{red}(u)$ and $\mathrm{res}_2(t)=1$, and for every place $V'$ with $P.\mathrm{reduceFst}\,V'=w$ that is strict on neither side, the order $V'.\mathrm{ord}\,t$ equals the coefficient at $V'$ of the divisor $\sigma\cdot V-V$.
--
--   This is the tube equation on an annulus lying over a node of the reduction of $X_0(Nq)$: it produces, for each place $V$ of the tube, a function $t$ with prescribed residues on the two prolongations whose divisor inside the tube is the inertial displacement $\sigma V-V$. It is used in [`ModularCurve.PlaceSpecialization.exists_goodRep_admissible_smul_single_sub_self_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_goodRep_admissible_smul_single_sub_self_of_isModel) to represent the action of inertia on degree-zero divisor classes by admissible divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_tubeEquation_smul_sub_self_of_annulus.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_tubeEquation_smul_sub_self_of_annulus
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (w : Place k (modularFunctionFieldC k N))
    (An : Annulus A ↥(modularFunctionFieldBar (N * q)))
    (hdom : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V' ∈ An.dom ↔ (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))
    (hmod : ((An.modulus : AlgebraicClosure ℚ) ≠ 0))
    (hσZ : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • An.param = An.param)
    (hZ₁ : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((An.modulus : AlgebraicClosure ℚ))⁻¹
        * An.param ∈ R.R₁.integers)
    (hZ₂ : An.param ∈ R.R₂.integers)
    (hZ₂0 : R.residue₂ ⟨An.param, hZ₂⟩ ≠ 0)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : V ∈ An.dom) :
    ∃ (x : A) (u : (↥A)ˣ) (t : ↥(modularFunctionFieldBar (N * q))) (h₁ : t ∈ R.R₁.integers) (h₂ : t ∈ R.R₂.integers),
      x ∈ IsLocalRing.maximalIdeal A ∧ (∃ d ∈ IsLocalRing.maximalIdeal A, x * d = An.modulus) ∧
      σ (x : AlgebraicClosure ℚ) = ((u : A) : AlgebraicClosure ℚ) * (x : AlgebraicClosure ℚ) ∧
      V.HasValue An.param (x : AlgebraicClosure ℚ) ∧
      t = (An.param - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (σ (x : AlgebraicClosure ℚ)))
          * (An.param - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (x : AlgebraicClosure ℚ))⁻¹ ∧
      (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k ↥(modularFunctionFieldC k N) (red (u : A)) ∧
      (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N)) = 1 ∧
      ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') →
        V'.ord t = ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V' := by sorry
