-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_lemma_20
-- name    : HiddenHardCoreColoring.Mixing.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:01:05.3833+00:00
-- url     : https://prove2.me/theorems/e47ac277-8b4d-43ec-a78b-0381bfa7bb3f
-- title:
--   Lemma 20 — variance part of the displacement, with an absolute constant C₀
-- statement:
--   There is an absolute constant $C_0>0$ such that the following holds for every finite simple graph on $n\ge1$ vertices with $\deg(v)\le\Delta$ and every $q$ with $q\ge\Delta+3$ and $q\ge(1+1/e)\Delta$: for every $a>0$ and every $f\in L^2(\mu)$,
--   $$\sum_{c\in[q]}V_c\big(f-\tilde f_c\big)\le\frac{C_0a}{q-\Delta}\Big(\|Lf\|_\mu^2+\langle f,Lf\rangle_\mu\Big)+\frac{C_0a^2}{(q-\Delta)^2}\langle f,Lf\rangle_\mu .$$
--   The proof (p.29) gives $C_0=2.2\cdot10^5$.
--
--   This bounds the variance cross term in the proof of Lemma 8.
--
--   Differences from the source:
--   - reading: there is an absolute constant C₀ → ∃ C₀ > 0 chosen before the graph, Δ, q, a and f; reason: 'absolute' means independent of all these parameters; requiring C₀ > 0 loses nothing since the bound is monotone in C₀
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Lemma 20, p.22; proof §7.5, pp.28–29 (C₀ = 2.2·10⁵)

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Hidden

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Lemma 20** (Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.22). There is an absolute constant `C₀` such that, whenever
`q ≥ (1 + 1/e)Δ` (and the standing `deg ≤ Δ`, `q ≥ Δ + 3`), for every `a > 0` and every `f`,
`∑_c V_c(f − f̃_c) ≤ C₀a/(q − Δ)(‖Lf‖²_µ + ⟨f, Lf⟩_µ) + C₀a²/(q − Δ)² ⟨f, Lf⟩_µ`. -/
theorem lemma_20 :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (Δ q : ℕ), (∀ v, G.degree v ≤ Δ) → Δ + 3 ≤ q → (1 + 1 / Real.exp 1) * (Δ : ℝ) ≤ (q : ℝ) →
        ∀ (a : ℝ), 0 < a → ∀ f : Col G q → ℝ,
          ∑ c : Fin q, Vc G q c (f - smooth G c a f) ≤
            C₀ * a / ((q : ℝ) - (Δ : ℝ)) * (sqNorm G q (Lap G q *ᵥ f) + ip G q f (Lap G q *ᵥ f)) +
              C₀ * a ^ 2 / ((q : ℝ) - (Δ : ℝ)) ^ 2 * ip G q f (Lap G q *ᵥ f) := by sorry

end HiddenHardCoreColoring.Mixing
