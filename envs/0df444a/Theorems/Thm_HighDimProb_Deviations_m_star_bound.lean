-- Prove2me | Theorems.Thm_HighDimProb_Deviations_m_star_bound
-- name    : HighDimProb.Deviations.m_star_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:09:42.868231+00:00
-- url     : https://prove2.me/theorems/bb7d1caf-7e24-4292-93f0-9cadd246dfb2
-- title:
--   Theorem 9.4.2 — The $M^*$ bound
-- statement:
--   This is the **$M^*$ bound**, a direct geometric consequence of the matrix deviation
--   inequality: the expected diameter of the intersection of a fixed set $T$ with a random
--   subspace $E = \ker A$ of codimension $m$ is controlled by the Gaussian width of $T$.
--
--   Let $T\subseteq\mathbb R^n$ and let $A$ be an $m\times n$ matrix whose rows are independent,
--   isotropic, sub-gaussian random vectors with $K := \max_i\|A_i\|_{\psi_2}$. Then the random
--   subspace $E = \ker A$ satisfies
--   $$
--   \mathbb E\,\mathrm{diam}(T\cap E) \;\le\; \frac{CK^2 w(T)}{\sqrt m},
--   $$
--   where $w(T)$ is the Gaussian width of $T$ (`GaussianWidth`) and $C$ is an absolute constant.
--
--   **Formalization Note** `ker A` at a sample point $\omega$ is represented as $\{x :
--   \forall i, \langle A_i(\omega),x\rangle = 0\}$, the set of $x$ with $A(\omega)x=0$, without a
--   separate construction of $A(\omega)$ as a linear map. `diam` is `Metric.diam`
--   ($0$ on an unbounded set); `Bornology.IsBounded T` guards this, matching every use of this
--   theorem in the book ($T$ a bounded geometric set). `Integrable … ∧ ∫ … ≤ …` states the
--   expectation is finite and bounded, guarding the same non-integrable-defaults-to-$0$ trap as
--   Theorem 9.1.1's mean-zero hypothesis. $w(T)$ is given the same explicit-real-witness treatment
--   as $\gamma(T)$ in Theorem 9.1.1. The hypothesis $m > 0$ is added: the conclusion divides by
--   $\sqrt m$, and Lean's real division convention ($x/0 = 0$) would otherwise make the bound
--   trivially $0$ at $m=0$ regardless of $C,K,w(T)$, which is false whenever $T$ has positive
--   diameter — the book's own proof ("Dividing by $\sqrt m$ yields …", p. 241) already implicitly
--   assumes $m\ge 1$, matching every other use of $m$ in the chapter as a positive row count.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 241, Theorem 9.4.2

import Mathlib
import Definitions.Def_HighDimProb_Deviations_IsIsotropic
import Definitions.Def_HighDimProb_Deviations_SubgaussianVectorNorm
import Definitions.Def_HighDimProb_Deviations_GaussianWidth

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Deviations

/-- **Theorem 9.4.2** (`M*` bound), Vershynin, *High-Dimensional Probability* (2018), p. 241
(PDF p. 249).

"Consider a set `T ⊂ ℝⁿ`. Let `A` be an `m × n` matrix whose rows `Aᵢ` are independent, isotropic
and sub-gaussian random vectors in `ℝⁿ`. Then the random subspace `E = ker A` satisfies
`E diam(T ∩ E) ≤ CK²w(T)/√m`, where `K = maxᵢ‖Aᵢ‖_{ψ2}`."

Same representation of `A`, isotropy and the sub-gaussian bound `K` as `matrix_deviation_
inequality` (Theorem 9.1.1, whose proof this theorem is a direct consequence of, per the book's
own one-line proof). `ker A` at a sample point `ω` is `{x | ∀ i, ⟨Aᵢ(ω), x⟩ = 0}`, exactly the set
of `x` with `A(ω)x = 0` in `ℝᵐ` (`(A(ω)x)ᵢ = ⟨Aᵢ(ω),x⟩`), avoiding a separate construction of the
matrix `A(ω)` as a linear map. `diam` is `Metric.diam` (`ℝ`-valued, `0` on an unbounded set —
trap 3 of `reference/FAITHFULNESS_TRAPS.md`); `Bornology.IsBounded T` guards this, since `T ∩
ker A(ω) ⊆ T` is then bounded for every `ω`, matching every use of this theorem in the book
(`T` a bounded geometric set, e.g. a subset of a sphere or a convex body). `Integrable … ∧ ∫ … ≤
…` (not the bare inequality) states "`E diam(T ∩ E)` is finite and bounded by the right side",
guarding the same non-integrable-defaults-to-`0` trap as the mean-zero hypothesis of Theorem
9.1.1. The right-hand side's `w(T)` is made an explicit real witness `w` with `gaussianWidth T =
(w : EReal)`, the same finiteness pattern Theorem 9.1.1 uses for `γ(T)`. `C` is existentially
quantified before every type, instance and hypothesis it is uniform over. `hm : 0 < m` is added
because the conclusion divides by `√m`: at `m = 0` the row family is empty (every hypothesis on
`A` holds vacuously), `ker A(ω) = Set.univ` for every `ω`, and `Real.sqrt 0 = 0` makes the
right-hand side `0` regardless of `C, K, w` via Lean's `x / 0 = 0` convention, making the
statement false (not merely vacuous) whenever `diam(T) > 0`. The book's own proof ("Dividing by
`√m` yields …", p. 241) implicitly assumes `m ≥ 1`, matching every other use of `m` in the
chapter as a positive count of measurement rows. -/
theorem m_star_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {m n : ℕ} (hm : 0 < m) (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)),
        iIndepFun A P →
        (∀ i, IsIsotropic P (A i)) →
        ∀ (K : ℝ), 0 ≤ K → (∀ i, subgaussianVectorNorm P (A i) ≤ K) →
        ∀ (T : Set (EuclideanSpace ℝ (Fin n))), Bornology.IsBounded T →
        ∀ (w : ℝ), gaussianWidth T = (w : EReal) →
          Integrable
              (fun ω => Metric.diam (T ∩ {x | ∀ i, inner (𝕜 := ℝ) (A i ω) x = 0})) P ∧
          ∫ ω, Metric.diam (T ∩ {x | ∀ i, inner (𝕜 := ℝ) (A i ω) x = 0}) ∂P ≤
            C * K ^ 2 * w / Real.sqrt (m : ℝ) := by sorry

end HighDimProb.Deviations
