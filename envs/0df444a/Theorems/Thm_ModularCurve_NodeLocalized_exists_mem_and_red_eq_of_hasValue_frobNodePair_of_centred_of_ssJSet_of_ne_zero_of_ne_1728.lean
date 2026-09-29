-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_mem_and_red_eq_of_hasValue_frobNodePair_of_centred_of_ssJSet_of_ne_zero_of_ne_1728
-- name    : ModularCurve.NodeLocalized.exists_mem_and_red_eq_of_hasValue_frobNodePair_of_centred_of_ssJSet_of_ne_zero_of_ne_1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/f591d75a-518e-5fa7-ae48-75f07aa77a5d
-- title:
--   Residue at a centred place over a supersingular node
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ (the Lean `AlgebraicClosure ℚ`), let $k$ be an algebraically closed field of characteristic $q$, and let $\mathrm{red}\colon A\to k$ be a ring homomorphism whose vanishing locus is exactly the maximal ideal of $A$, i.e. $\mathrm{red}\,c=0$ iff $c\in\mathfrak{m}_A$. Let $a\in k$ lie in `ssJSet q k`, meaning that every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero point killed by $q$, and assume $a^{q^2}=a$, $a\neq 0$ and $a\neq 1728$. Let $f$ belong to `modularFunctionFieldBar (1 * q)`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $1\cdot q$ inside $\overline{\mathbb{Q}}$-Laurent series. Assume: $f$, viewed as a Laurent series, lies in the localisation `CharPReduction.modularLocalized (1 * q) A.toSubring red` of the level-$(1\cdot q)$ modular ring at the kernel of $\mathrm{red}$, its image under `CharPReduction.modularRedLocHom` lies in `modularFunctionFieldC k 1`, which is $k(\,\overline{j},\overline{j}_1)$, and is nonzero; and the same three conditions hold for the image of $f$ under the Fricke involution `frickeInvolutionBar (1 * q)`. Call a place $W$ of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb{Q}}$ (a proper valuation subring containing the base field, with principal ideals) centred at the pair $(a,a^q)$ if there are $x,y\in A$ with $\mathrm{red}\,x=a$, $\mathrm{red}\,y=a^q$ and $W.\mathrm{ord}(j-x)>0$, $W.\mathrm{ord}(j_q-y)>0$, where $j$ is the image of the $q$-expansion `jq` under the coefficient embedding and $j_q$ that of `qExpand ℚ (1 * q) jq`, and $\mathrm{ord}$ is minus the logarithm of the associated adic valuation. Assume $W.\mathrm{ord}\,f=0$ for every centred place, let $W$ itself be centred, and let $c\in k$ be a value of the reduction $\langle\,\cdot\,\rangle$ of $f$ at the first component `charLGeomPlaceOfPoint k a` of `frobNodePair q a`, in the sense that the reduced function lies in that place's valuation subring and its residue is the image of $c$. Then $W.\mathrm{evalAt}\,f$, the residue value of $f$ at $W$ in $\overline{\mathbb{Q}}$, belongs to $A$ and $\mathrm{red}$ of it equals $c$.
--
--   This is the pointwise compatibility of the $A$-residue with the value on the near branch at a supersingular node of the characteristic-$q$ reduction of $X_0(q)$: the hypothesis $a\in$ `ssJSet q k` restricts attention to supersingular $j$-invariants, where the two branches of the plane model genuinely cross. It is used by [`ModularCurve.NodeLocalized.isUnit_evalAt_of_forall_centred_ord_eq_zero_of_gaussUnit`](thm.html#ModularCurve.NodeLocalized.isUnit_evalAt_of_forall_centred_ord_eq_zero_of_gaussUnit) in the analysis of functions with no zero or pole on the node tube.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_mem_and_red_eq_of_hasValue_frobNodePair_of_centred_of_ssJSet_of_ne_zero_of_ne_1728.lean

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

theorem ModularCurve.NodeLocalized.exists_mem_and_red_eq_of_hasValue_frobNodePair_of_centred_of_ssJSet_of_ne_zero_of_ne_1728
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (hq : 5 ≤ q)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1)
    (h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))))
    (c : k) (hc₁ : (frobNodePair q a).1.HasValue (⟨_, h₁F⟩ : modularFunctionFieldC k 1) c) :
    ∃ hmem : W.evalAt f ∈ A, red ⟨W.evalAt f, hmem⟩ = c := by sorry
