-- Prove2me | Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
-- name    : ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/209c2df5-12fb-5428-8277-23630eec1e3a
-- title:
--   q-expansion function field of Γ₀(M) equals ℚ(j(qᵈ):d∣ M)
-- statement:
--   Let $M$ be a nonzero natural number. Two intermediate fields of the extension $\mathbb{Q} \subseteq \mathbb{Q}((q))$ (Laurent series over $\mathbb{Q}$) are compared. The first, `qExpFunctionFieldC ℚ (Gamma0 M)`, is the subfield generated over $\mathbb{Q}$ by the set `intFormRatiosC ℚ (Gamma0 M)` of those Laurent series of the form $\mathrm{intSeriesC}_{\mathbb{Q}}(p_f)/\mathrm{intSeriesC}_{\mathbb{Q}}(p_g)$, where for some weight $k \in \mathbb{Z}$ there are modular forms $f, g$ of weight $k$ for the image of $\Gamma_0(M) \le \mathrm{SL}_2(\mathbb{Z})$ in $\mathrm{GL}_2(\mathbb{R})$ and integral power series $p_f, p_g \in \mathbb{Z}[[q]]$ with `IsIntegralQExp f pf` and `IsIntegralQExp g pg`, subject to $\mathrm{intSeriesC}_{\mathbb{Q}}(p_g) \neq 0$. The second, `modularFunctionFieldFull M`, is the subfield generated over $\mathbb{Q}$ by the set `divisorExpansions M` of Laurent series $\mathrm{qExpand}_{\mathbb{Q}}\, d\, \mathrm{jq}$, for $d$ a nonzero divisor of $M$, i.e. by the $q$-expansions of $j$ in the variable $q^{d}$. The assertion is that these two intermediate fields coincide.
--
--   This is the classical identification of the field of modular functions for $\Gamma_0(M)$, rational over $\mathbb{Q}$, with $\mathbb{Q}(j(q^d) : d \mid M)$, realised inside $\mathbb{Q}((q))$ via $q$-expansions. It is the link between the two models of the modular curve used in the formalisation, the one built from ratios of modular forms with integral $q$-expansions on $\Gamma_0(M)$ and the one built from expansions of $j$, and it is cited throughout the subsequent development of $X_0(M)$ and its Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve CongruenceSubgroup in

theorem ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull (M : ℕ) [NeZero M] :
    qExpFunctionFieldC ℚ (Gamma0 M) = modularFunctionFieldFull M := by sorry
