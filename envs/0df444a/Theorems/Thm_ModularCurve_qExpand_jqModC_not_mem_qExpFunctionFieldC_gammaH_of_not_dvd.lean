-- Prove2me | Theorems.Thm_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_of_not_dvd
-- name    : ModularCurve.qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/8c1dc763-8a47-596b-a8ed-9533291aa84a
-- title:
--   j(qᵈ) not in the q-expansion function field of Γ_{H'}(N)
-- statement:
--   Let $K$ be a field, let $N\ge 1$ and let $H'$ be a subgroup of $(\mathbb{Z}/N)^\times$, and assume that the image of $N$ in $K$ is nonzero. Let $d\ge 1$ be such that $d\nmid N$ and the image of $d$ in $K$ is nonzero. Write $\Gamma_{H'}(N)$ for [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H'$ under the homomorphism `gamma0Units N` sending $\gamma\in\Gamma_0(N)$ to the unit of $\mathbb{Z}/N$ given by its lower-right entry. Let `jqModC K` be the Laurent series $q^{-1}\cdot(E_4^3\eta^{-24})$, the $q$-expansion of the modular invariant $j$ with coefficients pushed into $K$, and let `qExpand K d` be the ring endomorphism of $K((q))$ multiplying exponents by $d$, so that `qExpand K d (jqModC K)` is $j(q^d)$. Finally let `qExpFunctionFieldC K Γ` be the intermediate field of $K((q))$ generated over $K$ by all quotients $f/g$ of Laurent series over $K$ arising from integral $q$-expansions $p_f,p_g\in\mathbb{Z}[[q]]$ of modular forms $f,g$ of some common weight $k$ for $\Gamma$ (viewed inside $\mathrm{GL}_2(\mathbb{R})$), with the image of $p_g$ in $K((q))$ nonzero. The assertion is that $j(q^d)$ does not lie in `qExpFunctionFieldC K (CohCarrier.GammaH N H')`.
--
--   This is the non-membership statement used to see that $j(q^d)$ generates a strictly larger field than the $q$-expansion function field of the modular curve of level $\Gamma_{H'}(N)$ exactly when $d\nmid N$; both arithmetic hypotheses are needed, since for $d\mid N$ the series $j(q^d)$ already lies in the field, and if $d$ vanishes in $K$ (for instance $d=\operatorname{char}K$) then $j(q^d)$ is a Frobenius power of $j(q)$. It is invoked in the construction of polynomial relations over base-changed Laurent series fields for $\Gamma_0$-type levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_of_not_dvd
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (hNK : ((N : ℕ) : K) ≠ 0)
    (d : ℕ) [NeZero d] (hd : ¬ d ∣ N) (hdK : ((d : ℕ) : K) ≠ 0) :
    ModularCurve.qExpand K d (ModularCurve.jqModC K) ∉ ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H') := by sorry
