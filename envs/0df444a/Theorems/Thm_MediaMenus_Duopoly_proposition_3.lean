-- Prove2me | Theorems.Thm_MediaMenus_Duopoly_proposition_3
-- name    : MediaMenus.Duopoly.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:52.562276+00:00
-- url     : https://prove2.me/theorems/d3b126e6-1448-4097-8819-f8f8bdffc0b0
-- title:
--   Proposition 3, p. 18 — in the unique duopoly equilibrium both platforms set the two-item menu with a^L = (w − d^L)/3, a^H = α/3, and both types multi-home
-- statement:
--   Consider the duopoly of two ad-supported platforms with two-item price/advertising menus (§2, §4.2), with consumer types $L,H$ of advertising disutility $0<d^L<d^H$, type-$H$ probability $r\in(0,1)$, substitutability $\gamma\in(0,1)$, base value $v>0$ and maximum ad value $w>d^L$. Let $\rho=(1-\gamma)/(1+\gamma)$ and $\alpha=(w-d^H-(1-r)(d^H-d^L)/r)^+$, and define the two menu items
--   $$(s^L,a^L)=\Big(\tfrac{\rho v^2}{2}-d^La^L-(d^H-d^L)a^H,\ \tfrac{w-d^L}{3}\Big),\qquad (s^H,a^H)=\Big(\tfrac{\rho v^2}{2}-d^Ha^H,\ \tfrac{\alpha}{3}\Big).$$
--   Then:
--   1. **Existence.** The profile in which both platforms offer the menu $\{(s^L,a^L),(s^H,a^H)\}$ and each type $\theta$ multi-homes with item $(s^\theta,a^\theta)$ on both platforms is an equilibrium.
--   2. **Two items.** $(s^L,a^L)\ne(s^H,a^H)$.
--   3. **Uniqueness.** In every equilibrium, each platform's menu consists exactly of the two items $(s^L,a^L)$ and $(s^H,a^H)$, and each type $\theta$ multi-homes and chooses $(s^\theta,a^\theta)$ on each platform.
--   4. **Revenue.** In every equilibrium each platform's expected revenue is
--   $$\frac{\rho v^2}{2}+\frac{(1-r)(w-d^L)^2+r\alpha^2}{9}.$$
--
--   This is the paper's main duopoly result: competition with menus leads to symmetric, separating menus on which every consumer uses both platforms, which is the basis for the paper's comparisons of monopoly and duopoly prices and of the value of menu differentiation.
--
--   **Formalization Note.** Equilibrium is `IsEquilibrium` of the model file, which writes out the concept the paper's proofs use: consumers maximize utility, multi-home and participate on ties (Lemma 4 C, p. 37; p. 53); a deviating platform may pick any admissible menu and the most favourable consumer response; a type that uses the rival platform before and after the deviation keeps her item there (p. 55). Without the last two tie rules the existence part is false. The strategy space is two-item menus (p. 47, after Lemma 7); "the unique equilibrium" is read as uniqueness of the chosen items and of the menus as sets, up to which slot holds which item. Two hypotheses are added to the page's standing assumptions: $v>0$ (Lemma 6 A's optimal consumption $v/(1+\gamma)$ is nonnegative; p. 37 uses $\gamma v^2/(1+\gamma)>0$) and $w>d^L$ (otherwise the stated $a^L=(w-d^L)/3$ is negative, contradicting $a\ge0$; the proofs of Propositions 2 and 4 write $w>d^L$, and the consumer-choice step on p. 53 uses $a^L>a^H$).
-- source:
--   DeValve & Pekeč, Optimal Price/Advertising Menus for Two-Sided Media Platforms, SSRN 2715531 (version of 2021-04-15), p. 18, Proposition 3 (proof pp. 52–59)

import Mathlib
import Definitions.Def_MediaMenus_Duopoly_Model

namespace MediaMenus.Duopoly

theorem proposition_3 (P : Params) (hS : P.Standing) :
    IsEquilibrium P (fun _ => eqMenu P) eqChoice ∧
    eqItem P .L ≠ eqItem P .H ∧
    (∀ (M : Profile) (c : Ty → Choice), IsEquilibrium P M c →
      (∀ i, Set.range (M i) = {eqItem P .L, eqItem P .H}) ∧
      ∀ θ, ∃ k₀ k₁, c θ = .multi k₀ k₁ ∧ M 0 k₀ = eqItem P θ ∧ M 1 k₁ = eqItem P θ) ∧
    (∀ (M : Profile) (c : Ty → Choice), IsEquilibrium P M c → ∀ i,
      expRev P M i c =
        rho P * P.v ^ 2 / 2 + ((1 - P.r) * (P.w - P.dL) ^ 2 + P.r * alphaQ P ^ 2) / 9) := by sorry

end MediaMenus.Duopoly
