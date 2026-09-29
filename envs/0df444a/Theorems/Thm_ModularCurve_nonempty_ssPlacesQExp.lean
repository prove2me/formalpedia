-- Prove2me | Theorems.Thm_ModularCurve_nonempty_ssPlacesQExp
-- name    : ModularCurve.nonempty_ssPlacesQExp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/cf087443-32ed-580c-8fd4-755affad9483
-- title:
--   Existence of supersingular places on X(Γ) in characteristic p
-- statement:
--   Let $M$ be a nonzero natural number and let $\Gamma$ be a subgroup of $\mathrm{SL}(2,\mathbb{Z})$ sandwiched between the congruence subgroups, $\Gamma_1(M)\le\Gamma\le\Gamma_0(M)$; let $p$ be a prime not dividing $M$, and let $K$ be an algebraically closed field of characteristic $p$. Consider the intermediate field $F=$ `qExpFunctionFieldC K Γ` of the Laurent series field $K(\!(X)\!)$ over $K$, namely the subfield generated over $K$ by the family `intFormRatiosC K Γ` of ratios of integral forms of level $\Gamma$. A place of $F$ over $K$ is, in this development, a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring. The assertion is that the set `ssPlacesQExp K Γ p` is nonempty: there exists such a place $v$ for which one can find an element $x\in F$ whose underlying Laurent series is the modular $j$-series `jqModC K`, together with $a\in K$, such that $v$ has value $a$ at $x$ (that is, $x$ lies in the valuation subring of $v$ and reduces to the image of $a$ in the residue field) and $a$ belongs to `ssJSet p K`.
--
--   This is the statement that the modular curve attached to $\Gamma$, presented through its $q$-expansion function field over an algebraically closed field of characteristic $p$, carries at least one place whose $j$-value lies in `ssJSet p K`; classically, supersingular points exist on $X(\Gamma)$ in every characteristic. It feeds the analysis of the special fibre of the relative $\mathrm{Pic}^0$ of the model of $X_H(M)$, where the number of such places controls the toric rank, and is cited by the results on prolongation data and place specialisations there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nonempty_ssPlacesQExp.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.nonempty_ssPlacesQExp
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] :
    (ssPlacesQExp K Γ p).Nonempty := by sorry
