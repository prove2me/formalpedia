-- Prove2me | Theorems.Thm_NetFeePlatform_Competition_proposition_4
-- name    : NetFeePlatform.Competition.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:06.216508+00:00
-- url     : https://prove2.me/theorems/7ab9af4d-ed32-4cb9-86db-5919e01786ac
-- title:
--   Proposition 4, p. 18 — for 2 ln 2 + 4/3 < γ ≤ 27/8, some triopoly equilibrium has a platform larger than every platform of every duopoly equilibrium
-- statement:
--   **Competition may increase dominance.**
--
--   Consider the one-sided Logit platform game with no outside option, in which platforms are ex ante identical: common marginal cost $c$, common interaction value $\gamma$, no interoperability. With $J$ platforms and net fees $t=(t^1,\dots,t^J)$, platform $j$'s share is $n^j(t)=e^{-t^j}/\sum_k e^{-t^k}$ and its profit is $\pi^j(t)=(t^j+\gamma n^j(t)-c)\,n^j(t)$; an equilibrium is a pure-strategy Nash equilibrium in net fees. Assume
--   $$2\ln2+\frac43<\gamma\le\frac{27}{8}.$$
--
--   Then
--   1. duopoly ($J=2$) has an equilibrium; and
--   2. there exist an equilibrium $t_3$ under triopoly ($J=3$) and a platform $i$ such that for every duopoly equilibrium $t_2$ and every platform $k$ of the duopoly,
--   $$n^k(t_2)<n^i(t_3).$$
--
--   In words, adding a third platform can produce an equilibrium whose dominant platform has a larger market share than any platform has in any duopoly equilibrium: more competition can increase market dominance when network effects are strong.
--
--   **Formalization Note** The paper states the range $\gamma\in(2.71,3.375]$. The upper end $27/8=3.375$ is exact. The lower end is replaced by $2\ln2+\tfrac43\approx2.7196$: at the symmetric duopoly equilibrium the paper's own criterion $g(1/2;3)-g(1/2;2)>0$ is equivalent to $\gamma>2\ln2+\tfrac43$, and for $\gamma$ in $(2.71,\,2\ln2+\tfrac43]$ a numerical check finds only the symmetric duopoly equilibrium and no triopoly equilibrium with a share above $1/2$, so the printed statement appears false there. Conclusion 1 is not printed in the proposition; it is the existence claim of Proposition 2′ for this case and is included so that the comparison with "any duopoly equilibrium" is not vacuous. The dominant platform's index $i$ is existential. "No outside option" is the outside-option weight $w=e^{z}=0$.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 18, Proposition 4 (§5.1); standing assumptions of §5, pp. 17–18; proof pp. 49–50

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.Competition
theorem proposition_4 (c γ : ℝ) (hlo : 2 * Real.log 2 + 4 / 3 < γ) (hhi : γ ≤ 27 / 8) :
    (∃ t₂ : Fin 2 → ℝ, IsEquilibrium 0 c γ 0 t₂) ∧
    ∃ t₃ : Fin 3 → ℝ, IsEquilibrium 0 c γ 0 t₃ ∧ ∃ i : Fin 3,
      ∀ t₂ : Fin 2 → ℝ, IsEquilibrium 0 c γ 0 t₂ →
        ∀ k : Fin 2, demand 0 t₂ k < demand 0 t₃ i := by sorry
end NetFeePlatform.Competition
