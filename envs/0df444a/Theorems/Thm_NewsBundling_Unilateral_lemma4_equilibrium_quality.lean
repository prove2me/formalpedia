-- Prove2me | Theorems.Thm_NewsBundling_Unilateral_lemma4_equilibrium_quality
-- name    : NewsBundling.Unilateral.lemma4_equilibrium_quality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:53.632642+00:00
-- url     : https://prove2.me/theorems/e2d615da-1d10-4cd0-848f-1f3b7aed7377
-- title:
--   Lemma 4, p. 12 — equilibrium quality on both sides of $c^\dagger$
-- statement:
--   Under Table 1's assumptions, a subgame-perfect equilibrium of the content-bundling game exists. Every equilibrium quality $q^*$ equals $q_L(c)=\phi_1/c$ when $c>c^\dagger$, and equals $q_H(c)=(\beta-\Lambda\phi_1)/(c(1-\Lambda))$ when $c<c^\dagger$. At the crossover,
--
--   $$c=c^\dagger\quad\Longrightarrow\quad q^*\in\{q_L(c),q_H(c)\},$$
--
--   and an equilibrium exists at each of these two qualities. This is the quality characterization used in Proposition 1.
--
--   **Formalization Note** The printed lemma assigns $q_L$ at $c=c^\dagger$ as a tie-break. The underlying game has both equilibrium qualities there; the formal statement records both rather than building an unmentioned selection rule into subgame perfection.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 12, Lemma 4; App. A, p. 31, proof of Lemma 4

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting

namespace NewsBundling.Unilateral

/-- Lemma 4, p. 12: all equilibrium qualities, including both at the crossover. -/
theorem lemma4_equilibrium_quality (β φ0 φ1 c Λ : ℝ)
    (h : StandingAssumptions β φ0 φ1 c Λ) :
    (∃ σ, IsSPE β φ0 φ1 c Λ σ) ∧
    (∀ σ, IsSPE β φ0 φ1 c Λ σ →
      (cdagger β φ1 Λ < c → σ.quality = qL φ1 c) ∧
      (c < cdagger β φ1 Λ → σ.quality = qH β φ1 c Λ) ∧
      (c = cdagger β φ1 Λ →
        σ.quality = qL φ1 c ∨ σ.quality = qH β φ1 c Λ)) ∧
    (c = cdagger β φ1 Λ →
      (∃ σ, IsSPE β φ0 φ1 c Λ σ ∧ σ.quality = qL φ1 c) ∧
        ∃ σ, IsSPE β φ0 φ1 c Λ σ ∧ σ.quality = qH β φ1 c Λ) := by sorry

end NewsBundling.Unilateral
