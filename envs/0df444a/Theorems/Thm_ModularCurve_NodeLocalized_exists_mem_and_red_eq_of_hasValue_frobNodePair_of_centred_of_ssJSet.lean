-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_mem_and_red_eq_of_hasValue_frobNodePair_of_centred_of_ssJSet
-- name    : ModularCurve.NodeLocalized.exists_mem_and_red_eq_of_hasValue_frobNodePair_of_centred_of_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/79eb917c-b8e8-54de-be32-f26003aa301d
-- title:
--   Residue compatibility at a supersingular node of X₀(q)
-- statement:
--   Fix a prime $q$ with $q\ge 5$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$ (with decidable equality) and a ring homomorphism $\mathrm{red}\colon A\to k$ whose kernel is exactly the maximal ideal of $A$. Let $a\in k$ satisfy $a^{q^{2}}=a$ and lie in `ssJSet q k`, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero affine point killed by $q$. Let $f$ lie in `modularFunctionFieldBar (1 * q)`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $1\cdot q$, viewed inside Laurent series over $\overline{\mathbb{Q}}$. Assume that $f$ and its image under `frickeInvolutionBar (1 * q)` both lie in `CharPReduction.modularLocalized (1 * q) A.toSubring red`, the localisation of the level-$q$ modular ring with coefficients in $A$ at the complement of the kernel of coefficientwise reduction, and that their images under `CharPReduction.modularRedLocHom (1 * q) A.toSubring red` are nonzero and lie in `modularFunctionFieldC k 1`, the subfield of Laurent series over $k$ generated over $k$ by `jqModC k` and `jqNModC k 1`. Call a place $W$ of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb{Q}}$ (a valuation subring containing $\overline{\mathbb{Q}}$, proper, with principal ideals) centred at $(a,a^{q})$ if there are $x,y\in A$ with $\mathrm{red}\,x=a$, $\mathrm{red}\,y=a^{q}$ and $W.\mathrm{ord}$ positive on the images in `modularFunctionFieldBar (1 * q)` of `jq` minus $x$ and of `qExpand ℚ (1 * q) jq` minus $y$ respectively. Assume $W'.\mathrm{ord}\,f=0$ for every centred place $W'$, and let $W$ be a centred place. Let $c\in k$ be such that the reduction of $f$, as an element of `modularFunctionFieldC k 1`, has value $c$ at the first component of `frobNodePair q a`, that is at the project's place `charLGeomPlaceOfPoint k a`: the reduction lies in that place's valuation subring and its residue is the image of $c$. The conclusion is that the value `W.evalAt f`, obtained by inverting $\overline{\mathbb{Q}}\to$ residue field on the residue of $f$ at $W$, lies in $A$ and its image under $\mathrm{red}$ equals $c$.
--
--   This is the pointwise comparison, at a place of the characteristic-zero modular function field of level $q$ centred at the supersingular node $(a,a^{q})$ of the mod-$q$ fibre, between the $A$-value of a function regular along both branches and the value of its reduction at the corresponding place on the near branch; the supersingularity hypothesis on $a$ is what rules out the ordinary $\mathbb{F}_{q^{2}}$-points, where the two branches separate. It is used in the analysis of the places centred at $j=0$ and $j=1728$, namely by [`ModularCurve.NodeLocalized.isUnit_evalAt_zero_of_gaussPair_of_isAlgClosed`](thm.html#ModularCurve.NodeLocalized.isUnit_evalAt_zero_of_gaussPair_of_isAlgClosed) and [`ModularCurve.NodeLocalized.isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed`](thm.html#ModularCurve.NodeLocalized.isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_mem_and_red_eq_of_hasValue_frobNodePair_of_centred_of_ssJSet.lean

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

theorem ModularCurve.NodeLocalized.exists_mem_and_red_eq_of_hasValue_frobNodePair_of_centred_of_ssJSet
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (hq : 5 ≤ q)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
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
