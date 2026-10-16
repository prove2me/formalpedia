-- Prove2me | Theorems.Thm_NewsBundling_Unilateral_proposition1
-- name    : NewsBundling.Unilateral.proposition1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:54.079983+00:00
-- url     : https://prove2.me/theorems/9c63e0e8-fb29-4b81-9751-0e54c9f6d785
-- title:
--   Proposition 1, p. 12 — effect of unilateral content bundling
-- statement:
--   A newspaper chooses quality $q$, a platform chooses a news share $\lambda\le\Lambda$, and consumers allocate their time between the two sites. Assume $0<\phi_0,\phi_1<1$, $\phi_1<\beta$, $c>2\beta$, and $0<\Lambda<1/2$, with the revenues, cost, utility, and subgame-perfect equilibrium defined by the baseline model. Equilibria exist with and without bundling. For every bundling equilibrium and every benchmark equilibrium with $\Lambda=0$, publisher profit is strictly lower with bundling. Away from the crossover threshold
--
--   $$c^\dagger=\frac{\beta+\phi_1(1-2\Lambda)}{2\Lambda(1-\Lambda)},$$
--
--   equilibrium quality and consumer surplus are each strictly higher with bundling if and only if $c<c^\dagger$:
--
--   $$\pi_1^*<\hat\pi_1,\qquad c\ne c^\dagger\ \Longrightarrow\ \bigl(q^*>\hat q\iff c<c^\dagger\bigr)\ \text{and}\ \bigl(CS^*>\widehat{CS}\iff c<c^\dagger\bigr).$$
--
--   At $c=c^\dagger$ there is also a bundling equilibrium whose quality is below the benchmark quality. The result identifies when diverted consumption reduces or raises the publisher's quality investment, while its profit still falls.
--
--   **Formalization Note** The paper's Lemma 4 selects the low-quality equilibrium at the crossover, but both low- and high-quality equilibria exist. The $c\ne c^\dagger$ qualification applies only to the two “if and only if” comparisons. Publisher profit falls at every equilibrium, including at the crossover. Equilibrium existence is explicit, and the benchmark uses the same subgame-perfect equilibrium predicate with $\Lambda=0$.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 12, Proposition 1; App. A, p. 31, proof of Proposition 1

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting

namespace NewsBundling.Unilateral

/-- Proposition 1, p. 12, with the c = c† equilibrium multiplicity made explicit. -/
theorem proposition1 (β φ0 φ1 c Λ : ℝ)
    (h : StandingAssumptions β φ0 φ1 c Λ) :
    (∃ σ, IsSPE β φ0 φ1 c Λ σ) ∧
    (∃ σb, IsSPE β φ0 φ1 c 0 σb) ∧
    (∀ σ σb, IsSPE β φ0 φ1 c Λ σ →
      IsSPE β φ0 φ1 c 0 σb →
        eqProfit β φ1 c σ < eqProfit β φ1 c σb ∧
        (c ≠ cdagger β φ1 Λ →
          (σb.quality < σ.quality ↔ c < cdagger β φ1 Λ) ∧
          (consumerSurplus σb < consumerSurplus σ ↔ c < cdagger β φ1 Λ))) ∧
    (c = cdagger β φ1 Λ →
      ∀ σb, IsSPE β φ0 φ1 c 0 σb →
        ∃ σ, IsSPE β φ0 φ1 c Λ σ ∧ σ.quality < σb.quality) := by sorry

end NewsBundling.Unilateral
