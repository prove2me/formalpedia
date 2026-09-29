-- Prove2me | Theorems.Thm_ModularCurve_exists_ssAnnulus_centred_of_widthOne
-- name    : ModularCurve.exists_ssAnnulus_centred_of_widthOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/f540621f-28c1-5868-9fbc-c51a0fe0e0c2
-- title:
--   Annulus of places centred at a width-one supersingular crossing
-- statement:
--   Let $q$ be a prime with $5 \le q$, let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $k$ be an algebraically closed field of characteristic $q$ with decidable equality, and let $\mathrm{red} : A \to k$ be a ring homomorphism whose zero set is exactly the maximal ideal of $A$ (hypothesis `hker`). Let $a \in k$ lie in `ssJSet q k`, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero point killed by $q$, and assume $a^{q^2} = a$, $a \neq 0$ and $a \neq 1728$. Write $J$ for the class in the intermediate field $\mathrm{modularFunctionFieldBar}(1\cdot q) \subseteq \mathrm{LaurentSeries}(\overline{\mathbb Q})$ of the coefficientwise image of the Laurent series `jq`, and $J_q$ for the class of the image of `qExpand ℚ (1*q) jq` (the same series with exponents multiplied by $q$). Then there exist two annuli $An$, $An'$ over $A$ in $\mathrm{modularFunctionFieldBar}(1\cdot q)$ — each consisting of a set of places of that field over $\overline{\mathbb Q}$, a parameter, and a modulus in the maximal ideal of $A$, subject to the annulus axioms: every place in the set is rational with parameter value a nonzero element of the maximal ideal dividing the modulus, each such admissible value is attained by a unique place of the set, the parameter minus its value has order $1$ at each such place, and functions of order $0$ throughout the set are, up to a constant and a power of the parameter, units at every place of the set — such that: $An'$ and $An$ have the same set of places and the same modulus; that modulus is nonzero in $\overline{\mathbb Q}$; the product of the two parameters equals the image of the modulus in the function field; the common set of places consists exactly of those places $W$ for which there are $x, y \in A$ with $\mathrm{red}\,x = a$, $\mathrm{red}\,y = a^q$, $W.\mathrm{ord}(J - x) > 0$ and $W.\mathrm{ord}(J_q - y) > 0$; the parameter of $An$ is $J_q - J^q$; and the modulus of $An$ is the image of $q$ in $A$.
--
--   This is the width-one case of the Deligne–Rapoport description of $X_0(q)$ near a supersingular point of its reduction, where the local equation is $xy = q$: the places reducing to the crossing $(a, a^q)$ form an annulus with parameter $J_q - J^q$ and modulus $q$, together with its companion for the other branch, obtained from the Kronecker congruence for the modular polynomial. It supplies the annular charts used in the construction of semistable models and in the computation of crossing exponents for place prolongations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ssAnnulus_centred_of_widthOne.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.exists_ssAnnulus_centred_of_widthOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    ∃ (An An' : Annulus A ↥(modularFunctionFieldBar (1 * q))),
      (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
        ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
        An'.param * An.param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
              ((An.modulus : AlgebraicClosure ℚ))) ∧
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        W ∈ An.dom ↔
          ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) ∧
      An.param = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q ∧
      An.modulus = ((q : ℕ) : A) := by sorry
