-- Prove2me | Theorems.Thm_ModularCurve_relfinrank_x1HeckeCompositum_eq_mul
-- name    : ModularCurve.relfinrank_x1HeckeCompositum_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/b464ea0c-e702-596f-8287-18dd82c783b2
-- title:
--   Degree of the Hecke compositum over X₁(M) factorises
-- statement:
--   Let $L$ be a field equipped with a $\mathbb Q$-algebra structure, let $M$, $\ell$, $\ell'$ be nonzero natural numbers, and assume $\ell$ and $\ell'$ are coprime. For a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb Z)$ write $F(\Gamma) = \mathbb Q(\mathrm{intFormRatiosC}\ \mathbb Q\ \Gamma) \subseteq \mathbb Q((q))$ for the subfield of the Laurent series field generated over $\mathbb Q$ by the set [`ModularCurve.intFormRatiosC`](def/ModularCurve_X1.html#L83) attached to $\Gamma$, and write $L\cdot F(\Gamma) \subseteq L((q))$ for `laurentBaseChange`, the subfield generated over $L$ by the image of $F(\Gamma)$ under the coefficientwise map $\mathbb Q((q)) \to L((q))$ induced by $\mathbb Q \to L$. Put $K = L\cdot F(\Gamma_1(M))$ and $K_t = L\cdot F(\Gamma_1(M) \cap \Gamma_0(t))$, and let $\sigma_\ell =$ `qExpand L ℓ` be the ring endomorphism of $L((q))$ multiplying all exponents by $\ell$, i.e. $q \mapsto q^{\ell}$. With $\mathrm{relfinrank}\ A\ B$ denoting the degree of $B$ over $A \sqcap B$, the assertion is the equality of natural numbers
--   $$\bigl[\,K_{M\ell} \sqcup L(\sigma_\ell(K_{M\ell'})) : L(\sigma_\ell(K))\,\bigr] = \bigl[\,K_{M\ell'} : K\,\bigr]\cdot\bigl[\,K_{M\ell} : L(\sigma_\ell(K))\,\bigr],$$
--   where $L(\sigma_\ell(A))$ is the subfield of $L((q))$ generated over $L$ by the image of $A$ under $\sigma_\ell$, the compositum $\sqcup$ is the join of intermediate fields of $L((q))/L$, and each bracket is the corresponding `relfinrank`.
--
--   This is the linear disjointness, over the field of functions on $X_1(M)$ pulled back along $\tau \mapsto \ell\tau$, of the two degeneracy covers of $X_1(M)$ coming from $\Gamma_1(M) \cap \Gamma_0(M\ell)$ and $\Gamma_1(M) \cap \Gamma_0(M\ell')$ for coprime $\ell,\ell'$, expressed as a multiplicativity of relative degrees of subfields of $L((q))$. It is the degree count behind the identification of the composite of the Hecke correspondences $T_\ell$ and $T_{\ell'}$ with a single correspondence, and is cited by [`ModularCurve.heckeOperatorOneBar_comm`](thm.html#ModularCurve.heckeOperatorOneBar_comm), the commutation $T_\ell T_{\ell'} = T_{\ell'} T_\ell$ on $J_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_relfinrank_x1HeckeCompositum_eq_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.relfinrank_x1HeckeCompositum_eq_mul (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (hℓ : Nat.Coprime ℓ ℓ') :
    IntermediateField.relfinrank
        (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
          (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M) :
            Set (LaurentSeries L))))
        (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ)) ⊔
          IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
            (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ')) :
              Set (LaurentSeries L))))
      = IntermediateField.relfinrank
            (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
            (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ')))
        * IntermediateField.relfinrank
            (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
              (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M) :
                Set (LaurentSeries L))))
            (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ))) := by sorry
