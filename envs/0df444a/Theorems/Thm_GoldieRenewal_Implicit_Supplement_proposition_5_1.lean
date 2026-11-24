-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_Supplement_proposition_5_1
-- name    : GoldieRenewal.Implicit.Supplement.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:15:07.85382+00:00
-- url     : https://prove2.me/theorems/4286b4c4-64a0-422c-8df3-936307a3c64e
-- title:
--   Proposition 5.1 — R̃ = ⋁ Q_kΠ_{k−1} is a.s. finite and its law is the unique law solving R =_L max(Q, MR)
-- statement:
--   Let $(Q,M)$ have joint law $\mu$, with $M\ge0$ a.s.,
--   $$
--   -\infty\le E\log M<0\qquad\text{and}\qquad E\log(1\vee Q)<\infty,
--   $$
--   where $\log0=-\infty$. Let $(Q_k,M_k)$, $k\ge1$, be i.i.d. with law $\mu$ and $\Pi_k:=M_1\cdots M_k$ ($\Pi_0=1$). Then
--   $$
--   \tilde R:=\bigvee_{k=1}^\infty Q_k\Pi_{k-1}
--   $$
--   is a.s. finite, and its law is the unique law for $R$ such that (1.2) holds: $R\overset{L}{=}\max(Q,MR)$ with $R$ independent of $(M,Q)$.
--
--   This is the existence and uniqueness step for the random extremal equation, obtained from Letac's principle; Theorem 5.2 is stated for this law.
--
--   **Formalization Note** "a.s. finite" is "the sequence $Q_k\Pi_{k-1}$ is a.s. bounded above" (it is never $-\infty$, its first term being $Q_1$); on that event Lean's real supremum is $\tilde R$. $E\log M$ is computed in $\overline{\mathbb R}$ from $E\log^+M$ and $E\log^-M$ with $\log0=-\infty$; "$-\infty\le E\log M<0$" is $E\log^+M<\infty$ together with $E\log M<0$. A law satisfying (1.2) is a probability measure fixed by the law operator of (1.2); uniqueness is among all probability laws on $\mathbb R$.
--
--   Differences from the source:
--
--   - encoding: R̃ is a.s. finite → a.s. the sequence Q_kΠ_{k−1} is bounded above, and R̃ is the real supremum; reason: the supremum is ≥ Q₁ > −∞, so finiteness is boundedness above
--   - encoding: −∞ ≤ E log M < 0 → E log⁺ M < ∞ and E log M < 0 in EReal, with log 0 = −∞; reason: E log M < 0 is only meaningful when E log⁺ M < ∞; the base mission encodes (2.6) the same way
--   - encoding: its law is the unique law such that (1.2) holds → the law of R̃ is fixed by the law operator of (1.2), and every probability law fixed by it equals the law of R̃; reason: (1.2) requires R independent of (M, Q), which the image of law(Q, M) ⊗ ρ encodes
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 138, Proposition 5.1; §5, p. 138

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_Supplement_Models

namespace GoldieRenewal.Implicit.Supplement

open MeasureTheory ProbabilityTheory

/-- **Proposition 5.1** (Goldie, *Implicit renewal theory and tails of solutions of random
equations*, Ann. Appl. Probab. 1(1) (1991), p. 138). Let `(Q, M)` have joint law `μ`, with
`M ≥ 0` a.s., `−∞ ≤ E log M < 0` and `E log(1 ∨ Q) < ∞`, and let `(Q_k, M_k)`, `k ≥ 1`, be i.i.d.
with law `μ`; `Π_k := M₁ ⋯ M_k`. Then `R̃ := ⋁_{k=1}^∞ Q_k Π_{k−1}` is a.s. finite, and its law is
the unique law for `R` such that (1.2) `R =_L max(Q, MR)`, `R` independent of `(M, Q)`, holds.

**Formalization Note** `μ` is a law on `ℝ × ℝ` with first coordinate `Q` and second `M`. The
sequence is stored 0-based (`QM i = (Q_{i+1}, M_{i+1})`). "`R̃` is a.s. finite" is "the sequence
`Q_k Π_{k−1}` is a.s. bounded above" (it is never `−∞`, its first term being `Q₁`); on that event
`extremalSup` is the paper's `R̃`. `E log M` is `logAbsMean` of the law of `M` (`log|M| = log M` for
`M ≥ 0`, with `log 0 = −∞`), computed in `EReal`; "`−∞ ≤ E log M < 0`" is
`E log⁺ M < ∞` (needed for the expectation to exist and be `< 0`) and `E log M < 0`.
`E log(1 ∨ Q)` is a lower Lebesgue integral. A law satisfying (1.2) is a probability measure fixed by
`extremalOperator μ`. -/
theorem proposition_5_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (QM : ℕ → Ω → ℝ × ℝ) (hQM : ∀ i, Measurable (QM i))
    (hQM_indep : iIndepFun QM P) (hQM_law : ∀ i, P.map (QM i) = μ)
    (hM_nonneg : μ {p | p.2 < 0} = 0)
    (hlogM_plus : GoldieRenewal.Implicit.logPlusMoment (μ.map Prod.snd) < ⊤)
    (hlogM_neg : GoldieRenewal.Implicit.logAbsMean (μ.map Prod.snd) < 0)
    (hlogQ : ∫⁻ p, ENNReal.ofReal (Real.log (max 1 p.1)) ∂μ < ⊤) :
    (∀ᵐ ω ∂P, BddAbove (Set.range (fun i => extremalTerm QM i ω))) ∧
    extremalOperator μ (P.map (extremalSup QM)) = P.map (extremalSup QM) ∧
    ∀ ρ : ProbabilityMeasure ℝ, extremalOperator μ (ρ : Measure ℝ) = ρ →
      (ρ : Measure ℝ) = P.map (extremalSup QM) := by sorry

end GoldieRenewal.Implicit.Supplement
