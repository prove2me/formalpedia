-- Prove2me | Theorems.Thm_GnpColoring_lemma_3_18
-- name    : GnpColoring.lemma_3_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:12.2795+00:00
-- url     : https://prove2.me/theorems/f7f5a46e-92ab-4b0b-a597-4e2467fb2134
-- title:
--   Lemma 3.18 — tree blocks: $\lambda_{\max}(\Lambda_{B,\tau})\le1+\delta$
-- statement:
--   Let $0<\eta<\varepsilon\le1/2$ and $\delta>0$. There is $A_0$ such that for every $A\ge A_0$ and every $C>0$ there is $d_0$ such that for every $d\ge d_0$ and every integer $q\ge d+d^{1/2+\varepsilon}$ the following holds. For every graph $G$, every valid block partition of $G$ (Definition 3.2, parameters $d,\eta,A,C$, any $D$), every tree block $B$ and every feasible colouring $\tau$ of $V\setminus B$,
--
--   $$\lambda_{\max}(\Lambda_{B,\tau})\le1+\delta.$$
--
--   The port colours of a tree block are therefore nearly uncorrelated, which feeds the hypothesis of Corollary 3.15.
--
--   Differences from the source:
--   - encoding: "for every coloring $\tau$ on $V\setminus B$" → every feasible $\tau$; reason: $\Lambda_{B,\tau}$ and $\nu_{B,\tau}$ are defined only for feasible $\tau$
--   - reading: "provided that d and A are large enough" → $\exists A_0\,\forall A\ge A_0\,\forall C>0\,\exists d_0\,\forall d\ge d_0$, in the regime $0<\eta<\varepsilon\le1/2$, $q\ge d+d^{1/2+\varepsilon}$; reason: Section 3.5, p.24: A large depending on $\varepsilon,\eta$, then d large; the regime is the one the proof uses (p.29)
--   - encoding: $\lambda_{\max}(\Lambda_{B,\tau})\le1+\delta$ → variance inequality `PortCovBound`; reason: quadratic form of $\Lambda_{B,\tau}$ is a variance
--   - generalization: valid partitions for the diameter constant $D=D(\eta,A,C)$ fixed in Definition 3.2 before $d$ → every $D>0$, quantified after $d_0$, so the bound is uniform in $D$; reason: the proof (pp.26–29) never uses the diameter condition of Definition 3.2; taking $D=D(\eta,A,C)$ gives the source's statement
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Lemma 3.18, p.26

import Mathlib
import Definitions.Def_GnpColoring_IsTreeBlock
import Definitions.Def_GnpColoring_blocks
import Definitions.Def_GnpColoring_IsValidPartition
import Definitions.Def_GnpColoring_IsFeasible
import Definitions.Def_GnpColoring_PortCovBound

open scoped Classical
open Finset

namespace GnpColoring

/-- **Lemma 3.18 (tree block covariance operator eigenvalue bound).** For every `δ > 0` there is `A₀` such that for all `A ≥ A₀` and
`C > 0` there is `d₀` such that for all `d ≥ d₀` and all integers `q ≥ d + d^(1/2+ε)`: for every graph
`G`, every valid block partition `S`, every tree block `B` and every feasible colouring `τ` of
`V ∖ B`, `λ_max(Λ_{B,τ}) ≤ 1 + δ`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Lemma 3.18, p.26: "Consider any tree block B. Then, for every coloring τ on V ∖ B and every δ > 0, we have λ_max(Λ_{B,τ}) ≤ (1 + δ). provided that d and A are large enough."

**Formalization Note** "d and A large enough" follows Section 3.5, p.24: "we assume that A is
sufficiently large depending on the fixed parameters ε, η, and then take d sufficiently large";
the regime `0 < η < ε ≤ 1/2`, `q ≥ d + d^(1/2+ε)` is the one the proof of Lemma 3.18 uses (p.29).
`λ_max(Λ_{B,τ}) ≤ 1 + δ` is `PortCovBound` (variance form); `τ` ranges over feasible colourings
(the conditional law `ν_{B,τ}` is defined only for them). -/
theorem lemma_3_18 :
    ∀ ε η : ℝ, 0 < η → η < ε → ε ≤ 1 / 2 → ∀ δ : ℝ, 0 < δ →
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → ∀ C : ℝ, 0 < C →
    ∃ d₀ : ℝ, ∀ d : ℝ, d₀ ≤ d → ∀ q : ℕ, d + d ^ ((1 : ℝ) / 2 + ε) ≤ (q : ℝ) →
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (D : ℝ) (S : Finset (Fin n)),
      IsValidPartition G d η A C D S →
      ∀ B ∈ blocks G S, IsTreeBlock G B →
      ∀ x : Fin n → Fin q, IsFeasible G q B x → PortCovBound G q B x (1 + δ) := by sorry

end GnpColoring
