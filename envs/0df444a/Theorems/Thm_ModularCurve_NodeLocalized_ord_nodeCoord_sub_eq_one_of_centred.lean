-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_ord_nodeCoord_sub_eq_one_of_centred
-- name    : ModularCurve.NodeLocalized.ord_nodeCoord_sub_eq_one_of_centred
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/7e1b9508-4fdb-583c-8958-aa61435a5b89
-- title:
--   Node coordinate minus its value is a uniformiser at W
-- statement:
--   Fix a prime $q$ with $5 \le q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$, and a ring homomorphism $\mathrm{red} \colon A \to k$ whose kernel is exactly the maximal ideal of $A$ (hypothesis `hker`). Let $a \in k$ satisfy $a^{q^2} = a$, $a \neq 0$, $a \neq 1728$, and lie in `ssJSet q k`, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero affine point killed by $q$. Let $W$ be a place of the field $\mathrm{modularFunctionFieldBar}\,(1 \cdot q)$ over $\overline{\mathbb Q}$ — the subfield of $\overline{\mathbb Q}((x))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the full level-$(1\cdot q)$ modular function field — that is, a proper valuation subring containing $\overline{\mathbb Q}$ whose ideals are principal; $\mathrm{ord}_W$ is minus the logarithm of the associated height-one adic valuation. Write $J$ for the element $\mathrm{coeffEmb}\,jq$ (the $j$-expansion) and $J_q$ for $\mathrm{coeffEmb}(\mathrm{qExpand}\,(1\cdot q)\,jq)$. Assume $W$ is centred at the supersingular node with coordinates $(a, a^q)$: there are $x, y \in A$ with $\mathrm{red}\,x = a$, $\mathrm{red}\,y = a^q$, $\mathrm{ord}_W(J - x) > 0$ and $\mathrm{ord}_W(J_q - y) > 0$. Assume further that $c \in A$ is a value of $J_q - J^q$ at $W$, meaning $J_q - J^q$ lies in the valuation subring of $W$ and its residue is the image of $c$. Then $\mathrm{ord}_W\bigl(J_q - J^q - c\bigr) = 1$.
--
--   The assertion is that the node coordinate $j(q\tau) - j(\tau)^q$, shifted by its value, is a uniformiser at any place of the level-$q$ modular function field centred at a width-one supersingular node of $X_0(q)$. It feeds the construction of supersingular annuli and the local equations used to cut out closures of horizontal points through such a node, being cited by [`ModularCurve.exists_ssAnnulus_centred_of_widthOne`](thm.html#ModularCurve.exists_ssAnnulus_centred_of_widthOne) and by [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_tubeEquation_smul_sub_self`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_tubeEquation_smul_sub_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_ord_nodeCoord_sub_eq_one_of_centred.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
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

theorem ModularCurve.NodeLocalized.ord_nodeCoord_sub_eq_one_of_centred
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hW : ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) (c : A)
    (hGc : W.HasValue ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) (c : AlgebraicClosure ℚ)) :
    W.ord (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ)) = 1 := by sorry
