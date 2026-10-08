-- Prove2me | Theorems.Thm_IsingLTL_BeliefProp_lemma_4_3_root_magnetization
-- name    : IsingLTL.BeliefProp.lemma_4_3_root_magnetization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:47.515864+00:00
-- url     : https://prove2.me/theorems/d589b0f7-2de3-407d-9cc5-ce77e1fbc658
-- title:
--   Plus and free boundary conditions at depth $\ell$ change the root magnetization by $O(1/\ell)$ (Lemma 4.3)
-- statement:
--   Let $0<B_{\min}$, and let $\beta_{\max}$, $\Delta$ be finite. There is a constant $M=M(\beta_{\max},B_{\min},\Delta)$ such that the following holds. Let $\mathsf T$ be a conditionally independent tree with average offspring numbers bounded by $\Delta$, let $0\le\beta\le\beta_{\max}$, let $\ell\ge1$, and let $\underline B$ be a field with $B_i\ge B_{\min}$ for all $i\in\mathsf T(\ell)$. Then
--   $$\mathbb E\big\{m^{\ell,+}(\underline B)-m^{\ell,0}(\underline B)\big\}\le\frac M\ell,$$
--   where $m^{\ell,+/0}(\underline B)=\langle\mu^{\ell,+/0},x_\varnothing\rangle$ are the root magnetizations under plus and free boundary conditions on $\mathsf T(\ell)$.
--
--   This is the key estimate of the paper: on such trees, the effect of a plus boundary at depth $\ell$ on the root vanishes, uniformly in the tree law, even at low temperature where Gibbs measures are not unique.
--
--   **Formalization Note** The conditions $0\le\beta\le\beta_{\max}$, $B\ge B_{\min}$ on $\mathsf T(\ell)$ and $\ell\ge1$ come from Theorem 4.2 and the proof; the upper bound $B_{\max}$ in the lemma's sentence plays no role and is omitted. The conclusion also asserts that $m^{\ell,+}-m^{\ell,0}$ is a measurable function of the tree, so that the expectation is meaningful.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 12, Lemma 4.3, eq. (4.5) (with the setting of Theorem 4.2, p. 11)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_CondIndepTree

namespace IsingLTL.BeliefProp

open MeasureTheory

/-- **Lemma 4.3** (Dembo–Montanari, arXiv:0804.4726v3, p. 12, eq. (4.5)). Suppose `T` is a
conditionally independent infinite tree of average offspring numbers bounded by `Δ`. For
`0 < B_min`, `β_max` and `Δ` finite there is `M = M(β_max, B_min, Δ)` such that
`E{m^{ℓ,+}(B) − m^{ℓ,0}(B)} ≤ M/ℓ`, where `m^{ℓ,+/0}(B) = ⟨μ^{ℓ,+/0}, x_ø⟩` are the root
magnetizations under plus and free boundary conditions on `T`.

Formalization Note: the hypotheses not written in the lemma's sentence are those of Theorem 4.2
(p. 11) and of its proof: `0 ≤ β ≤ β_max`, `B_i ≥ B_min` on `T(ℓ)` and `ℓ ≥ 1`. The upper bound
`B_max` of the lemma's sentence plays no role (no hypothesis uses it, and `M` does not depend on
it), so it is omitted. `M` is chosen before the tree law, the field, `β` and `ℓ`. The field is a
nonrandom function of the word; requiring `B_w ≥ B_min` for all words of length `≤ ℓ` is
equivalent to requiring it on `T(ℓ)`, since values off the tree are never used. The conclusion
includes measurability of `ω ↦ m^{ℓ,+} − m^{ℓ,0}` (bounded by `2`), so the Bochner integral is the
expectation and not a junk value. -/
theorem lemma_4_3_root_magnetization (βmax Bmin Δ : ℝ) (hBmin : 0 < Bmin) :
    ∃ M : ℝ, ∀ (μ : Measure (List ℕ → ℕ)) [IsProbabilityMeasure μ], IsingLTL.FreeEntropy.IsCondIndepTree μ Δ →
      ∀ (β : ℝ) (B : List ℕ → ℝ) (ℓ : ℕ), 0 ≤ β → β ≤ βmax → 1 ≤ ℓ →
        (∀ w : List ℕ, w.length ≤ ℓ → Bmin ≤ B w) →
        Measurable (fun ω => rootMag ω β B ℓ true - rootMag ω β B ℓ false) ∧
          ∫ ω, (rootMag ω β B ℓ true - rootMag ω β B ℓ false) ∂μ ≤ M / ℓ := by sorry

end IsingLTL.BeliefProp
