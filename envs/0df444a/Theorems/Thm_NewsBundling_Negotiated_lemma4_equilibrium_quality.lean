-- Prove2me | Theorems.Thm_NewsBundling_Negotiated_lemma4_equilibrium_quality
-- name    : NewsBundling.Negotiated.lemma4_equilibrium_quality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:54.541009+00:00
-- url     : https://prove2.me/theorems/effddf80-005f-40e2-97f3-4119fe89e1c2
-- title:
--   Lemma 4, p. 12 — equilibrium quality under unilateral content bundling is q_L(c) if c > c†, q_H(c) if c < c†, both at c = c†
-- statement:
--   Assume the standing assumptions of Table 1: $\varphi_0,\varphi_1\in(0,1)$, $\beta>\varphi_1$, $c>2\beta$, $\Lambda\in(0,1/2)$. The baseline game with unilateral content bundling has a subgame-perfect equilibrium, and in every one the quality $q^*$ satisfies
--
--   $$q^*=\begin{cases} q_L(c)=\dfrac{\varphi_1}{c}, & c>c^\dagger,\\[2mm] q_H(c)=\dfrac{\beta-\Lambda\varphi_1}{c(1-\Lambda)}, & c<c^\dagger,\\[2mm] q_L(c)\text{ or }q_H(c), & c=c^\dagger,\end{cases}\qquad c^\dagger=\frac{\beta+\varphi_1(1-2\Lambda)}{2\Lambda(1-\Lambda)};$$
--
--   and at $c=c^\dagger$ both $q_L(c)$ and $q_H(c)$ are equilibrium qualities.
--
--   This is the unilateral side of part 2 of Proposition 5.
--
--   **Formalization Note** The paper writes "$q^*=q_L(c)$ if $c\ge c^\dagger$"; at $c=c^\dagger$ the publisher is indifferent between the two qualities, so the paper's "$\ge$" is a tie-break, and the statement records both equilibria. It restates, in the namespace `NewsBundling.Negotiated`, the same statement as the companion mission on unilateral content bundling.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 12, §4.2, Lemma 4; App. A, proof of Lemma 4, p. 31

import Mathlib
import Definitions.Def_NewsBundling_Negotiated_Setting

namespace NewsBundling.Negotiated

theorem lemma4_equilibrium_quality (β φ0 φ1 c Λ : ℝ)
    (h : NewsBundling.Unilateral.StandingAssumptions β φ0 φ1 c Λ) :
    (∃ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c Λ σ) ∧
      (∀ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c Λ σ →
        (NewsBundling.Unilateral.cdagger β φ1 Λ < c → σ.quality = NewsBundling.Unilateral.qL φ1 c) ∧
          (c < NewsBundling.Unilateral.cdagger β φ1 Λ → σ.quality = NewsBundling.Unilateral.qH β φ1 c Λ) ∧
          (c = NewsBundling.Unilateral.cdagger β φ1 Λ → σ.quality = NewsBundling.Unilateral.qL φ1 c ∨ σ.quality = NewsBundling.Unilateral.qH β φ1 c Λ)) ∧
      (c = NewsBundling.Unilateral.cdagger β φ1 Λ →
        (∃ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c Λ σ ∧ σ.quality = NewsBundling.Unilateral.qL φ1 c) ∧
          ∃ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c Λ σ ∧ σ.quality = NewsBundling.Unilateral.qH β φ1 c Λ) := by sorry

end NewsBundling.Negotiated
