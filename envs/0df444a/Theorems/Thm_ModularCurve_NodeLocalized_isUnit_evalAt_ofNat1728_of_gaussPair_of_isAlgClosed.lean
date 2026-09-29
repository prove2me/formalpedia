-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed
-- name    : ModularCurve.NodeLocalized.isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/6062eead-d492-59da-a919-c5b3992a9219
-- title:
--   Unit values of a Gauss pair at nodes centred at 1728
-- statement:
--   Fix a prime $q$ with $5 \le q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$, and a ring homomorphism $\mathrm{red} : A \to k$ whose kernel is exactly the maximal ideal of $A$ (hypothesis `hker`). Assume $1728 \in k$ lies in `ssJSet q k`, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $1728$ has no nonzero point killed by $q$. Let $f$ belong to `modularFunctionFieldBar (1 * q)`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $1\cdot q$ inside $\overline{\mathbb Q}$-Laurent series. Assume that $f$ and its image under `frickeInvolutionBar (1 * q)` both lie in the localisation `CharPReduction.modularLocalized (1 * q) A.toSubring red` of the modular ring at the complement of the kernel of reduction, and that both have nonzero image under `CharPReduction.modularRedLocHom`. Assume further that every place $W$ of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$ which is centred at the node, in the sense that some $x \in A$ with $\mathrm{red}\,x = 1728$ satisfies $W.\mathrm{ord}(j - x) > 0$ and some $y \in A$ with $\mathrm{red}\,y = 1728^q$ satisfies $W.\mathrm{ord}(j(q\tau) - y) > 0$, has $W.\mathrm{ord}(f) = 0$ (here $j$ and $j(q\tau)$ denote the Laurent series `jq` and `qExpand ℚ (1 * q) jq` transported by `coeffEmb`). Then for any such centred place $W$, the value $W.\mathrm{evalAt}\,f \in \overline{\mathbb Q}$ lies in $A$ and is a unit of $A$.
--
--   This is the two-sided maximum principle at the width-two centre $j = 1728$ for places localised at a supersingular node of the Deligne–Rapoport model of $X_0(q)$: an element of the function field with Gauss-unit data on both sides of the Fricke involution and order zero at all places centred at the node has unit value at each such place. It feeds the construction of crossing presentations of the node ring and the attachment of the opposite annulus to the chart at infinity at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_StandardAnnulus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (ha : (1728 : k) ∈ ssJSet q k) (hq : 5 ≤ q)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = (1728 : k) ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
            (∃ y : A, red y = (1728 : k) ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hW : ((∃ x : A, red x = (1728 : k) ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
            (∃ y : A, red y = (1728 : k) ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ∃ h : W.evalAt f ∈ A, IsUnit (⟨_, h⟩ : A) := by sorry
