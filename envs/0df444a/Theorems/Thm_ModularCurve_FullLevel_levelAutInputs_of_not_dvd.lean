-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_levelAutInputs_of_not_dvd
-- name    : ModularCurve.FullLevel.levelAutInputs_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/f229f3b3-8f49-5f89-9fe6-dd0285aa3684
-- title:
--   Existence of level automorphisms when q ∤ M'
-- statement:
--   Let $q$ be a prime and $M'$ a natural number with $q \nmid M'$. The assertion is the predicate [`ModularCurve.FullLevel.LevelAutInputs q M'`](def/ModularCurve_FullLevelJacobian.html#L220), which says: for every index $\zeta$ in the type `Idx q` and every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$, there exists an $\overline{\mathbb{Q}}$-algebra automorphism $\tau$ of the field `fieldBar q M'`, i.e. of `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')`, an intermediate field of $\overline{\mathbb{Q}}((t))$ over $\overline{\mathbb{Q}}$, such that `IsLevelAutBar q M' ζ γ τ` holds. The latter says: for every weight $k \in \mathbb{Z}$, all modular forms $f, g$ of weight $k$ for the group [`CohCarrier.GammaH (q ^ 2 * M') (levelH q M')`](def/CohCarrier_Level.html#L133) inside $\mathrm{GL}_2(\mathbb{R})$, all integral power series $p_f, p_g \in \mathbb{Z}[[X]]$ with `IsIntegralQExp f pf` and `IsIntegralQExp g pg` and with the rational series attached to $p_g$ nonzero, and every ring homomorphism $\iota : \overline{\mathbb{Q}} \to \mathbb{C}$ sending $\zeta$'s underlying element to $\exp(2\pi i/q)$, the image under $\iota$, applied coefficientwise, of the Laurent series $\tau(p_f/p_g)$, multiplied by the $q$-expansion of $g \mid_k \mathrm{conjElem}(q,\gamma)$, equals the $q$-expansion of $f \mid_k \mathrm{conjElem}(q,\gamma)$.
--
--   This is the existence of the level automorphisms of the function field of a geometric component of the modular curve of full level $q$ over $\Gamma_0(M')$: the automorphism $\tau$ attached to $\gamma$ realises pull-back of functions along the conjugate $\mathrm{conjElem}(q,\gamma)$ on the component labelled by $\zeta$, characterised through ratios of $q$-expansions. It supplies the hypothesis `LevelAutInputs` used to put the resulting action on degree-zero divisor classes, and hence on the Tate module at the auxiliary prime $q$, in the constructions of the full-level Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_levelAutInputs_of_not_dvd.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

theorem ModularCurve.FullLevel.levelAutInputs_of_not_dvd (q : ℕ) [Fact q.Prime] (M' : ℕ)
    (hqM' : ¬ q ∣ M') : ModularCurve.FullLevel.LevelAutInputs q M' := by sorry
