-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_tubeEquation_smul_sub_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/415c67cf-4938-524b-8f3c-6fdb6574cf2f
-- title:
--   Tube equation for the inertial displacement σ V-V
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$, together with modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` at level $(1,q)$, a place specialisation $P$ for these data and a level-one prolongation pair $R=(R_1,R_2)$ for $P$. Assume $\mathrm{red}\,c=0$ exactly for $c$ in the maximal ideal of $A$, that $q\ge 5$, and let $a\in k$ be a $j$-invariant lying in `ssJSet q k` (every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero $q$-torsion point) with $a^{q^2}=a$, $a\ne 0$, $a\ne 1728$. Let $\sigma$ be a $\mathbb Q$-automorphism of $\overline{\mathbb Q}$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`, and let $V$ be a place of the field $\overline{\mathbb Q}\!\cdot\!F_{1\cdot q}$ obtained by base change of the full modular function field of level $1\cdot q$, assumed centred at the crossing determined by $a$: there are $x,y\in A$ with $\mathrm{red}\,x=a$, $\mathrm{red}\,y=a^{q}$ and $\mathrm{ord}_V(j-x)>0$, $\mathrm{ord}_V(j_q-y)>0$, where $j$ and $j_q$ are the elements given by the coefficient embedding of the $q$-expansions $jq$ and $\mathrm{qExpand}_{\mathbb Q}(1\cdot q)\,jq$. Then there are $x\in A$, a unit $u\in A^{\times}$ and an element $t$ of the same field, integral for both valuation subrings $R_1$ and $R_2$, such that: $x$ lies in the maximal ideal of $A$ and $x\,d=q$ for some $d$ in that maximal ideal; $\sigma(x)=u\,x$; the function $G:=j_q-j^{q}$ is $V$-integral with residue the image of $x$; $t=(G-\sigma(x))(G-x)^{-1}$; the residue $R.\mathrm{residue}_1(t)$ in `modularFunctionFieldC k 1` equals the constant $\mathrm{red}\,u$ and $R.\mathrm{residue}_2(t)=1$; and for every place $W$ centred at the crossing in the same sense, $\mathrm{ord}_W(t)$ equals the value at $W$ of the divisor $\sigma\cdot\delta_V-\delta_V$, the action being that of `arithmeticGalois` on divisors.
--
--   This is the local equation, on the tube over a width-one supersingular double point of the Deligne–Rapoport special fibre of $X_0(q)$, of the inertial displacement divisor $\sigma V - V$: the tube coordinate $G=j_q-j^q$ takes a value $x$ with $q\in x\mathfrak m_A$ at the crossing, and the ratio $(G-\sigma x)/(G-x)$ has constant residues $\overline u$ and $1$ on the two components. It is the input at supersingular points for the construction of good representatives with admissible gluing data, cited by `exists_goodRep_admissible_smul_single_sub_self_of_eq_zero_or_eq` and `exists_goodRep_admissible_smul_single_sub_self_of_ne_zero_of_ne`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open scoped Pointwise

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_tubeEquation_smul_sub_self
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hV : ((∃ x : A, red x = a ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ∃ (x : A) (u : (↥A)ˣ) (t : ↥(modularFunctionFieldBar (1 * q))) (h₁ : t ∈ R.R₁.integers) (h₂ : t ∈ R.R₂.integers),
      x ∈ IsLocalRing.maximalIdeal A ∧ (∃ d ∈ IsLocalRing.maximalIdeal A, x * d = ((q : ℕ) : A)) ∧
      σ (x : AlgebraicClosure ℚ) = ((u : A) : AlgebraicClosure ℚ) * (x : AlgebraicClosure ℚ) ∧
      V.HasValue ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) (x : AlgebraicClosure ℚ) ∧
      t = (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (σ (x : AlgebraicClosure ℚ)))
          * (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))⁻¹ ∧
      (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k 1)) = algebraMap k ↥(modularFunctionFieldC k 1) (red (u : A)) ∧
      (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k 1)) = 1 ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) →
        W.ord t = ((arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) W := by sorry
