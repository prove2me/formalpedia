-- Prove2me | Theorems.Thm_HighDimProb_Deviations_m_star_bound_v2
-- name    : HighDimProb.Deviations.m_star_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:55.49126+00:00
-- url     : https://prove2.me/theorems/d524fb9e-def9-4c58-86b4-a4ec114b06cc
-- title:
--   Theorem 9.4.2 — The $M^*$ bound: $\mathbb E\,\mathrm{diam}(T\cap\ker A)\le CK^2w(T)/\sqrt m$
-- statement:
--   This is the **$M^*$ bound**, a direct geometric consequence of the matrix deviation inequality: the expected diameter of the intersection of a fixed set $T$ with a random subspace $E=\ker A$ of codimension at most $m$ is controlled by the Gaussian width of $T$.
--
--   There is an absolute constant $C>0$ such that the following holds. Let $T\subseteq\mathbb R^n$ be a bounded set with Gaussian width $w(T)\in\mathbb R$ (`gaussianWidth`), and let $A$ be an $m\times n$ random matrix ($m\ge1$) whose rows $A_1,\dots,A_m$ are independent, isotropic, sub-gaussian random vectors with $\max_i\|A_i\|_{\psi_2}\le K$, where $\|\cdot\|_{\psi_2}$ is the sub-gaussian norm of a random vector (companion definition `subgaussianVectorNorm`, valued in $[0,\infty]$, finite exactly for sub-gaussian random vectors). Then the random subspace $E=\ker A$ satisfies
--   $$
--   \mathbb E\,\mathrm{diam}(T\cap E)\;\le\;\frac{CK^2\,w(T)}{\sqrt m},
--   $$
--   the expectation being finite.
--
--   **Formalization Note.** The retired version was disproved because its real-valued sub-gaussian norm returned the junk value $0$ for a heavy-tailed row, so an isotropic but non-sub-gaussian row satisfied the hypothesis with $K=0$ and the right-hand side collapsed to $0$. The new statement uses the corrected `ℝ≥0∞`-valued `subgaussianVectorNorm` (built on the corrected scalar norm) with $K\in[0,\infty)$ (`ℝ≥0`), so $\forall i,\ \|A_i\|_{\psi_2}\le K$ now says that every row *is* a sub-gaussian random vector with norm at most $K$, as the book's "sub-gaussian random vectors … $K=\max_i\|A_i\|_{\psi_2}$" does (any upper bound $K$ is what the proof uses). Everything else is as before: $\ker A$ at a sample point $\omega$ is $\{x:\forall i,\ \langle A_i(\omega),x\rangle=0\}$; `Metric.diam` is guarded by `Bornology.IsBounded T` (an unbounded $T$ has $w(T)=+\infty$, so nothing is lost); $w(T)$ is given by an explicit real witness since `gaussianWidth` is `EReal`-valued ($w(T)=+\infty$ makes the book's bound trivial, $T=\emptyset$ is degenerate); "$\mathbb E\,\mathrm{diam}$ is bounded" is stated as `Integrable ∧ ∫ ≤ …`; $m\ge1$ because the conclusion divides by $\sqrt m$ (the book's "dividing by $\sqrt m$"); $C$ is existentially quantified before every other object; isotropy is `IsIsotropic` (Definition 3.2.1 via Lemma 3.2.3).
-- source:
--   Vershynin, High-Dimensional Probability (CUP 2018), Theorem 9.4.2, p. 241 (PDF p. 249); sub-gaussian random vectors Definition 3.4.1, p. 56

import Mathlib
import Definitions.Def_HighDimProb_Deviations_IsIsotropic
import Definitions.Def_HighDimProb_Deviations_SubgaussianVectorNorm_v2
import Definitions.Def_HighDimProb_Deviations_GaussianWidth

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HighDimProb.Deviations

/-- **Theorem 9.4.2** (`M*` bound), Vershynin, *High-Dimensional Probability* (2018), p. 241
(PDF p. 249).

"Consider a set `T ⊂ ℝⁿ`. Let `A` be an `m × n` matrix whose rows `Aᵢ` are independent, isotropic
and sub-gaussian random vectors in `ℝⁿ`. Then the random subspace `E = ker A` satisfies
`E diam(T ∩ E) ≤ CK²w(T)/√m`, where `K = maxᵢ‖Aᵢ‖_{ψ2}`."

`ker A` at a sample point `ω` is `{x | ∀ i, ⟨Aᵢ(ω), x⟩ = 0}`; `diam` is `Metric.diam`;
`Bornology.IsBounded T` guards `Metric.diam`'s junk value `0` on unbounded sets (an unbounded `T`
has `w(T) = +∞` anyway, so nothing is lost); `Integrable … ∧ ∫ … ≤ …` states that
`E diam(T ∩ E)` is finite and bounded; `w(T)` is an explicit real witness with
`gaussianWidth T = (w : EReal)`; `hm : 0 < m` because the conclusion divides by `√m` (the book's
"dividing by `√m`" presupposes `m ≥ 1`).

Corrected version (`_v2`): the sub-gaussian bound uses the corrected `ℝ≥0∞`-valued
`subgaussianVectorNorm` (`⊤` for a non-sub-gaussian row) and `K : ℝ≥0`, so
`∀ i, ‖Aᵢ‖_{ψ₂} ≤ K` now states that every row *is* sub-gaussian with norm at most `K`. The
retired version's real-valued norm returned `0` for a heavy-tailed row, so an isotropic
non-sub-gaussian row satisfied the hypothesis with `K = 0` and the right-hand side collapsed to
`0`. -/
theorem m_star_bound_v2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {m n : ℕ} (hm : 0 < m) (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)),
        iIndepFun A P →
        (∀ i, IsIsotropic P (A i)) →
        ∀ (K : ℝ≥0), (∀ i, subgaussianVectorNorm P (A i) ≤ K) →
        ∀ (T : Set (EuclideanSpace ℝ (Fin n))), Bornology.IsBounded T →
        ∀ (w : ℝ), gaussianWidth T = (w : EReal) →
          Integrable
              (fun ω => Metric.diam (T ∩ {x | ∀ i, inner (𝕜 := ℝ) (A i ω) x = 0})) P ∧
          ∫ ω, Metric.diam (T ∩ {x | ∀ i, inner (𝕜 := ℝ) (A i ω) x = 0}) ∂P ≤
            C * K ^ 2 * w / Real.sqrt (m : ℝ) := by sorry

end HighDimProb.Deviations
