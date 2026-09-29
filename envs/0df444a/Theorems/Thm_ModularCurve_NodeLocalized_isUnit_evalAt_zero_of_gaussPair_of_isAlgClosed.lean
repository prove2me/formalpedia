-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_isUnit_evalAt_zero_of_gaussPair_of_isAlgClosed
-- name    : ModularCurve.NodeLocalized.isUnit_evalAt_zero_of_gaussPair_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/546bc1c6-23b0-5f5e-8820-920d3396dcc1
-- title:
--   Unit values of a Gauss pair at the node j=0
-- statement:
--   Let $q$ be a prime with $q \ge 5$, let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $k$ be an algebraically closed field of characteristic $q$, and let $\mathrm{red} : A \to k$ be a ring homomorphism whose zero set is exactly the maximal ideal of $A$ (hypothesis `hker`). Assume $0 \in$ `ssJSet q k`, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $0$ has no nonzero point killed by $q$. Let $f$ lie in the base change to $\overline{\mathbb Q}$ of the full modular function field of level $1\cdot q$ inside $\overline{\mathbb Q}$-Laurent series. Assume that the Laurent series of $f$ and of its image under `frickeInvolutionBar` both lie in `CharPReduction.modularLocalized`, the localisation of the modular ring at the prime of series reducing to $0$, and that both have nonzero image under the reduction homomorphism `CharPReduction.modularRedLocHom` to $k$-Laurent series. Assume further that for every place $W$ of this function field over $\overline{\mathbb Q}$ (a proper valuation subring containing the constants, with principal ideals) that is centred at the node — there are $x, y \in A$ with $\mathrm{red}\,x = 0$, $\mathrm{red}\,y = 0^q$ and both $j_q - x$ and $j_q(q\cdot) - y$ of positive order at $W$ — one has $W.\mathrm{ord}\,f = 0$. Then for any such centred place $W$, the value $W.\mathrm{evalAt}\,f$ lies in $A$ and is a unit there.
--
--   This is the two-sided Gauss maximum principle at the width-three centre $j = 0$ of the supersingular locus: a function whose reductions on both sides of the Fricke involution are nonzero, and which has order zero at every place centred at the node, takes unit values in $A$ at such places. It is the $a = 0$ case of the generic-centre form and feeds the crossing-presentation and chart-attachment statements for the annulus around the node in the Deligne–Rapoport model of $X_0(q)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_isUnit_evalAt_zero_of_gaussPair_of_isAlgClosed.lean

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

theorem ModularCurve.NodeLocalized.isUnit_evalAt_zero_of_gaussPair_of_isAlgClosed
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (ha : (0 : k) ∈ ssJSet q k) (hq : 5 ≤ q)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = (0 : k) ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
            (∃ y : A, red y = (0 : k) ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hW : ((∃ x : A, red x = (0 : k) ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
            (∃ y : A, red y = (0 : k) ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ∃ h : W.evalAt f ∈ A, IsUnit (⟨_, h⟩ : A) := by sorry
