-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_isUnit_evalAt_of_forall_centred_ord_eq_zero_of_gaussUnit
-- name    : ModularCurve.NodeLocalized.isUnit_evalAt_of_forall_centred_ord_eq_zero_of_gaussUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/92d1219a-5b71-5b6b-9202-8e47bbca2ecb
-- title:
--   Unit values at places centred on a supersingular node
-- statement:
--   Fix a prime $q \ge 5$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, and an algebraically closed field $k$ of characteristic $q$ together with a ring homomorphism $\mathrm{red} : A \to k$ whose vanishing locus is exactly the maximal ideal of $A$ (hypothesis `hker`). Let $a \in k$ satisfy $a \in$ `ssJSet q k`, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no point $P$ with $q \cdot P = 0$ other than $0$; assume further $a^{q^2} = a$, $a \neq 0$ and $a \neq 1728$. Let $f$ belong to `modularFunctionFieldBar (1 * q)`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $1 \cdot q$ inside Laurent series over $\overline{\mathbb{Q}}$. Assume that the Laurent series of $f$, and likewise that of its image under the Fricke involution `frickeInvolutionBar (1 * q)`, lie in `CharPReduction.modularLocalized (1 * q) A.toSubring red` — the subring of Laurent series of the form $r/s$ with $r, s$ in the modular ring over $A$ and $s$ outside the prime of series whose reduction vanishes — and that the reductions of both elements under `CharPReduction.modularRedLocHom` are nonzero Laurent series over $k$. Call a place $W$ of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb{Q}}$ (a proper valuation subring containing the base field whose ring is a principal ideal ring) centred at the pair $(a, a^q)$ if there are $x, y \in A$ with $\mathrm{red}\,x = a$, $\mathrm{red}\,y = a^q$, such that $W.\mathrm{ord}(J - x) > 0$ and $W.\mathrm{ord}(J_q - y) > 0$, where $J$ is the function given by the Laurent series `jq` and $J_q$ by its image under `qExpand ℚ (1 * q)`, and $\mathrm{ord}$ is minus the logarithm of the adic valuation of the place. Assume $W.\mathrm{ord}\,f = 0$ for every such centred place. Then for any centred place $W$, the value $W.\mathrm{evalAt}\,f$ lies in $A$ and is a unit of $A$.
--
--   This is the unit principle on the tube of a supersingular crossing of the reduction of $X_0(q)$ at $q$: a function integral with nonzero reduction on both branches through the crossing (the second branch via the Fricke involution) and with no zero or pole centred there takes unit values at every place centred at the crossing. It is used in the construction and analysis of supersingular annuli and in the slope laws relating the two charts at such a crossing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_isUnit_evalAt_of_forall_centred_ord_eq_zero_of_gaussUnit.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.NodeLocalized.isUnit_evalAt_of_forall_centred_ord_eq_zero_of_gaussUnit
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
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
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ∃ h : W.evalAt f ∈ A, IsUnit (⟨_, h⟩ : A) := by sorry
