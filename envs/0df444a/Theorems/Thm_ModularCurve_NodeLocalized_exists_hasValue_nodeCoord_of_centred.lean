-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_hasValue_nodeCoord_of_centred
-- name    : ModularCurve.NodeLocalized.exists_hasValue_nodeCoord_of_centred
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/b0e7a785-4f5c-52ec-8256-0a27ee1e4e81
-- title:
--   Node coordinate j_q-j^q has a value in the annulus
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $A$ be a valuation subring of $\overline{\mathbb Q}$, and let $k$ be an algebraically closed field of characteristic $q$. Let $\mathrm{red}\colon A\to k$ be a ring homomorphism whose kernel is exactly the maximal ideal of $A$, in the sense that $\mathrm{red}\,c=0$ if and only if $c\in\mathfrak m_A$. Let $a\in k$ satisfy $a\in$ `ssJSet q k`, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero affine point killed by $q$; assume further $a^{q^2}=a$, $a\neq 0$ and $a\neq 1728$. Let $W$ be a place of the field `modularFunctionFieldBar (1 * q)` (the subfield of $\overline{\mathbb Q}((Q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the full modular function field of level $1\cdot q$), that is, a proper valuation subring containing $\overline{\mathbb Q}$ whose ideals are principal, with associated order function $\mathrm{ord}_W$. Write $j$ for the element given by the Laurent expansion `jq` and $j_q$ for the one given by `qExpand ℚ (1 * q) jq`. Assume $W$ is centred at the node $(a,a^q)$: there are $x,y\in A$ with $\mathrm{red}\,x=a$, $\mathrm{red}\,y=a^q$, $\mathrm{ord}_W(j-x)>0$ and $\mathrm{ord}_W(j_q-y)>0$. Then there is $c\in\mathfrak m_A$ admitting $d\in\mathfrak m_A$ with $cd=q$ in $A$, such that $j_q-j^{\,q}$ lies in the valuation subring of $W$ and its residue is the image of $c$; i.e. $W$ takes the value $c$ on $j_q-j^{\,q}$.
--
--   This is the first step in the local analysis of a supersingular crossing on $X_0(q)$ in characteristic $q$: the function $G=j_q-j^{\,q}$ serves as a coordinate transverse to one branch at a width-one node, and the conclusion places its value $c$ strictly inside the annulus $0<v(c)<v(q)$, reflecting the Kronecker relation $G\cdot H=q\cdot(\text{unit})$ with $H=j-j_q^{\,q}$. It is used by the two-branch normalisation results that compute widths and orders of the geometric places lying over such a node.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_hasValue_nodeCoord_of_centred.lean

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

theorem ModularCurve.NodeLocalized.exists_hasValue_nodeCoord_of_centred
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
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ∃ c : A, c ∈ IsLocalRing.maximalIdeal A ∧ (∃ d ∈ IsLocalRing.maximalIdeal A, c * d = ((q : ℕ) : A)) ∧
      W.HasValue ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) (c : AlgebraicClosure ℚ) := by sorry
