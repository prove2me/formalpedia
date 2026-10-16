-- Prove2me | Theorems.Thm_NewsBundling_Negotiated_proposition5
-- name    : NewsBundling.Negotiated.proposition5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T02:44:02.60199+00:00
-- url     : https://prove2.me/theorems/8600ab71-614c-411f-9510-b77967fd1c48
-- title:
--   Proposition 5, p. 20 — negotiated content bundling raises quality over the benchmark iff c > β/Λ and over unilateral bundling iff c > c†
-- statement:
--   Let $\beta,\varphi_0,\varphi_1,c,\Lambda$ be real parameters with $\tfrac13<\beta\le1$, $\varphi_0,\varphi_1\in(0,1)$, $\varphi_1<\beta$, $c>2\beta$ and $\Lambda\in(0,1/2)$. Consider three games: the negotiated content-bundling game of §6 (Nash bargaining over a lump-sum fee, the platform keeping all ad revenue), the benchmark without content bundling (the baseline game with $\Lambda=0$), and the baseline game with unilateral content bundling at cap $\Lambda$. Write $\tilde q$, $\hat q$ and $q^*$ for the publisher's quality in a subgame-perfect equilibrium of each, and
--
--   $$c^\dagger=\frac{\beta+\varphi_1(1-2\Lambda)}{2\Lambda(1-\Lambda)}.$$
--
--   Then each of the three games has a subgame-perfect equilibrium, and for any equilibria of the three games:
--
--   1. if $\beta<1$, negotiated content bundling increases quality compared to the benchmark if and only if $c>\beta/\Lambda$:
--   $$\hat q<\tilde q\iff c>\frac{\beta}{\Lambda};$$
--   2. if $c\ne c^\dagger$, negotiated content bundling increases quality compared to unilateral content bundling if and only if $c>c^\dagger$:
--   $$q^*<\tilde q\iff c>c^\dagger.$$
--
--   The proposition evaluates the revenue-sharing policy adopted in Australia and France: a negotiated agreement raises news quality when quality is costly, the opposite of what unilateral content bundling does.
--
--   **Formalization Note** Two hypotheses are added to the page. (a) Part 1 is stated for $\beta<1$: at $\beta=1$, $q_1(c)=\hat q=\beta/c$, so for $c>(1+\beta)/(2\Lambda)$ the negotiated and benchmark qualities coincide although $c>\beta/\Lambda$. (b) Part 2 is stated for $c\ne c^\dagger$: at $c=c^\dagger$ the unilateral game has two equilibrium qualities $q_L<q_H$ (Lemma 4 selects $q_L$ by its "$c\ge c^\dagger$"), and the negotiated quality lies strictly between them, so the equivalence holds for one equilibrium and fails for the other. The benchmark and the unilateral game keep Table 1's $\varphi_0,\varphi_1$; footnote 16's $\varphi_0=1$, $\varphi_1=0$ describe only the negotiated game. The existence conjunct rules out a vacuous "for all equilibria" statement.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 20, Proposition 5; App. A, proof of Proposition 5, p. 33

import Mathlib
import Definitions.Def_NewsBundling_Negotiated_Setting

namespace NewsBundling.Negotiated

theorem proposition5 (β φ0 φ1 c Λ : ℝ) (hN : NegAssumptions β c Λ)
    (hU : NewsBundling.Unilateral.StandingAssumptions β φ0 φ1 c Λ) :
    ((∃ σ, IsNegotiatedSPE β c Λ σ) ∧ (∃ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c 0 σ) ∧
        (∃ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c Λ σ)) ∧
      ∀ σN σb σU, IsNegotiatedSPE β c Λ σN → NewsBundling.Unilateral.IsSPE β φ0 φ1 c 0 σb → NewsBundling.Unilateral.IsSPE β φ0 φ1 c Λ σU →
        (β < 1 → (σb.quality < σN.quality ↔ β / Λ < c)) ∧
          (c ≠ NewsBundling.Unilateral.cdagger β φ1 Λ → (σU.quality < σN.quality ↔ NewsBundling.Unilateral.cdagger β φ1 Λ < c)) := by sorry

end NewsBundling.Negotiated
