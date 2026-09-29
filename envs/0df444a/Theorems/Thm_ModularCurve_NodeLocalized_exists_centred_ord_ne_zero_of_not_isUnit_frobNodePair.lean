-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_centred_ord_ne_zero_of_not_isUnit_frobNodePair
-- name    : ModularCurve.NodeLocalized.exists_centred_ord_ne_zero_of_not_isUnit_frobNodePair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/c260263f-79da-52eb-86be-fe85c5329ab8
-- title:
--   Zero or pole at a place centred at a supersingular node
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$, and $k$ an algebraically closed field of characteristic $q$, and let $\mathrm{red} : A \to k$ be a ring homomorphism whose vanishing locus is exactly the maximal ideal of $A$ ($\mathrm{red}\,c = 0$ iff $c \in \mathfrak{m}_A$). Let $a \in k$ satisfy: $a \in \mathrm{ssJSet}\,q\,k$, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero affine point killed by $q$; $a^{q^2} = a$; $a \neq 0$; and $a \neq 1728$. Let $f$ lie in `modularFunctionFieldBar (1 * q)`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $1\cdot q$ inside Laurent series. Assume that $f$, as a Laurent series, lies in the subring `CharPReduction.modularLocalized (1 * q) A.toSubring red` (fractions $r/s$ with $r,s$ in the modular ring with coefficients in $A$ and $s$ outside the prime of coefficientwise reduction), that its image under the reduction homomorphism `CharPReduction.modularRedLocHom` lies in $\mathrm{modularFunctionFieldC}\,k\,1 = k(\mathrm{jqModC}\,k, \mathrm{jqNModC}\,k\,1)$, and that this image is nonzero; assume the same three conditions for the image of $f$ under the Fricke involution `frickeInvolutionBar (1 * q)`. Assume finally that the reduction of $f$, viewed in $\mathrm{modularFunctionFieldC}\,k\,1$, lies in the valuation subring of the first component $\mathrm{charLGeomPlaceOfPoint}\,k\,a$ of $\mathrm{frobNodePair}\,q\,a = (\mathrm{charLGeomPlaceOfPoint}\,k\,a, \mathrm{charLGeomPlaceOfPoint}\,k\,(a^q))$, but is not a unit of that ring. Then there is a place $W_0$ of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb{Q}}$ — a proper valuation subring containing $\overline{\mathbb{Q}}$ and a principal ideal ring — which is centred at the node in the sense that there are $x, y \in A$ with $\mathrm{red}\,x = a$, $\mathrm{red}\,y = a^q$, $W_0.\mathrm{ord}(j - x) > 0$ and $W_0.\mathrm{ord}(j_q - y) > 0$ (here $j$ is the coefficient embedding of `jq` and $j_q$ that of $\mathrm{qExpand}\,\mathbb{Q}\,(1\cdot q)\,\mathrm{jq}$, and $\mathrm{ord}$ is minus the logarithm of the associated adic valuation), and which satisfies $W_0.\mathrm{ord}\,f \neq 0$, i.e. $f$ has a zero or a pole at $W_0$. No lower bound such as $q \geq 5$ is imposed: for $q = 2, 3$ the hypotheses on $a$ are contradictory, by [`ModularCurve.eq_zero_of_mem_ssJSet_two`](thm.html#ModularCurve.eq_zero_of_mem_ssJSet_two) and [`ModularCurve.eq_zero_of_mem_ssJSet_three`](thm.html#ModularCurve.eq_zero_of_mem_ssJSet_three) together with $a \neq 0$.
--
--   This is the existence step in the study of the tube around a supersingular node of the reduction of $X_0(q)$ in characteristic $q$: a function whose near-branch reduction is a non-unit at the node must acquire nontrivial order at some place of the level-$q$ function field centred at that node. It is used by [`ModularCurve.NodeLocalized.ne_zero_of_hasValue_frobNodePair_of_forall_centred_ord_eq_zero`](thm.html#ModularCurve.NodeLocalized.ne_zero_of_hasValue_frobNodePair_of_forall_centred_ord_eq_zero) and its variant for supersingular $j$-invariants, which conclude in the contrapositive direction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_centred_ord_ne_zero_of_not_isUnit_frobNodePair.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.NodeLocalized.exists_centred_ord_ne_zero_of_not_isUnit_frobNodePair
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1)
    (h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hmem : (⟨_, h₁F⟩ : modularFunctionFieldC k 1) ∈ (frobNodePair q a).1.toValuationSubring)
    (hnu : ¬IsUnit (⟨_, hmem⟩ : (frobNodePair q a).1.toValuationSubring)) :
    ∃ W₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        ((∃ x : A, red x = a ∧
            0 < W₀.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W₀.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) ∧ W₀.ord f ≠ 0 := by sorry
