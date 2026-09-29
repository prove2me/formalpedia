-- Prove2me | Theorems.Thm_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charP
-- name    : ModularCurve.qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/e9468801-2627-5483-bd0b-ddd765eb248c
-- title:
--   j(qᵈ) not in the mod-ℓ level-Γ₁(N) expansion field
-- statement:
--   Let $\ell$ be a prime, let $K$ be an algebraically closed field of characteristic $\ell$, and let $N,d$ be non-zero natural numbers such that $\ell \nmid Nd$ and $d \nmid N$. Write $\mathrm{jqModC}\,K$ for the Laurent series $q^{-1}\cdot \overline{\mathrm{jNum}} \in K((q))$, where $\mathrm{jNum} = E_4^3 \cdot \mathrm{dedekindEtaUnitInv} \in \mathbb{Z}[[q]]$ and the bar denotes coefficientwise reduction along $\mathbb{Z} \to K$; write $\mathrm{qExpand}\,K\,d$ for the ring endomorphism of $K((q))$ that multiplies exponents by $d$, i.e. $q \mapsto q^d$. Let $\Gamma = \mathrm{GammaH}\,N\,\bot$ be the subgroup of $SL_2(\mathbb{Z})$ consisting of those matrices in $\Gamma_0(N)$ whose lower-right entry reduces to $1$ in $(\mathbb{Z}/N)^\times$, i.e. $\Gamma_1(N)$, and let $\mathrm{qExpFunctionFieldC}\,K\,\Gamma$ be the intermediate field of $K((q))$ generated over $K$ by all quotients $\mathrm{intSeriesC}\,K\,p_f / \mathrm{intSeriesC}\,K\,p_g$, where $f,g$ are modular forms of some common weight $k$ for $\Gamma$ (viewed inside $GL_2(\mathbb{R})$) admitting integral $q$-expansions $p_f,p_g \in \mathbb{Z}[[q]]$ in the sense of `IsIntegralQExp`, with $\mathrm{intSeriesC}\,K\,p_g \neq 0$. The conclusion is that $\mathrm{qExpand}\,K\,d\,(\mathrm{jqModC}\,K)$ does not belong to this field.
--
--   This is the core case — base field algebraically closed of characteristic $\ell$, level $\Gamma_1(N)$ — of the non-membership statement asserting that the reduced $j$-expansion in the variable $q^d$ generates a function field not contained in the level-$N$ one unless $d \mid N$. It is cited by [`ModularCurve.qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_of_not_dvd`](thm.html#ModularCurve.qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_of_not_dvd), from which the general level and base field case is obtained.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charP.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charP
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (N d : ℕ) [NeZero N] [NeZero d] (hℓ : ¬ ℓ ∣ N * d) (hd : ¬ d ∣ N) :
    ModularCurve.qExpand K d (ModularCurve.jqModC K) ∉ ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N ⊥) := by sorry
