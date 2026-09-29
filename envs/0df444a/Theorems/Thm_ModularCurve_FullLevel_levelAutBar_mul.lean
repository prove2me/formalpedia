-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
-- name    : ModularCurve.FullLevel.levelAutBar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/392d569c-8e9e-5cd5-b19a-409334fb8294
-- title:
--   Level automorphisms compose contravariantly: τ_{αβ}=τ_β∘τ_α
-- statement:
--   Let $q$ be a prime and $M'$ a natural number with $q \nmid M'$. Write $F =$ `fieldBar q M'`, the intermediate field `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')` of the Laurent series field $\overline{\mathbb{Q}}((t))$ over $\overline{\mathbb{Q}}$, and let $\zeta$ be an element of `Idx q`, that is a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$. For $\gamma \in \mathrm{SL}(2,\mathbb{Z})$ the automorphism `levelAutBar q M' ζ γ` $\in \mathrm{Aut}_{\overline{\mathbb{Q}}}(F)$ is defined by choice: it is some $\tau$ satisfying `IsLevelAutBar q M' ζ γ τ` if such a $\tau$ exists, and the identity otherwise; the predicate `IsLevelAutBar q M' ζ γ τ` requires that for every weight $k \in \mathbb{Z}$, all modular forms $f,g$ of weight $k$ on $\Gamma_H(q^2M')$ with $H =$ `levelH q M'`, all integral $q$-expansions $p_f, p_g$ of $f$ and $g$ with $p_g$ having nonzero image over $\mathbb{Q}$, and every ring embedding $\iota : \overline{\mathbb{Q}} \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, the identity $\iota\big(\tau(p_f/p_g)\big)\cdot q\text{-exp}\big(g\mid_k \mathrm{conjElem}\,q\,\gamma\big) = q\text{-exp}\big(f\mid_k \mathrm{conjElem}\,q\,\gamma\big)$ holds in $\mathbb{C}((t))$. The assertion is that for all $\alpha, \beta \in \mathrm{SL}(2,\mathbb{Z})$ lying in $\Gamma_0(M')$, the automorphism attached to $\alpha\beta$ equals `levelAutBar q M' ζ α` followed by `levelAutBar q M' ζ β`, i.e. $x \mapsto \tau_\beta(\tau_\alpha(x))$. The proof uses [`ModularCurve.FullLevel.levelAutInputs_of_not_dvd`](thm.html#ModularCurve.FullLevel.levelAutInputs_of_not_dvd), which supplies `LevelAutInputs q M'` from $q \nmid M'$.
--
--   This is the composition law for the action of $\Gamma_0(M')$ by level automorphisms on the function field of a geometric component of the modular curve of full level $q$ and $\Gamma_0(M')$-structure, contravariant because the automorphisms are pull-backs of functions along the conjugated matrices. It is used throughout the construction of the semistable covering data attached to these curves, in particular in the naturality statements relating the Igusa labelling of components to the $\Gamma_0(M')$-action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_levelAutBar_mul.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.levelAutBar_mul (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M')
    (ζ : ModularCurve.FullLevel.Idx q) (α β : SL(2, ℤ)) (hα : α ∈ CongruenceSubgroup.Gamma0 M')
    (hβ : β ∈ CongruenceSubgroup.Gamma0 M') :
    ModularCurve.FullLevel.levelAutBar q M' ζ (α * β) =
      (ModularCurve.FullLevel.levelAutBar q M' ζ α).trans (ModularCurve.FullLevel.levelAutBar q M' ζ β) := by sorry
