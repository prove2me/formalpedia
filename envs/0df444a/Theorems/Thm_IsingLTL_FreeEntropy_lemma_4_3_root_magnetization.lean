-- Prove2me | Theorems.Thm_IsingLTL_FreeEntropy_lemma_4_3_root_magnetization
-- name    : IsingLTL.FreeEntropy.lemma_4_3_root_magnetization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:53.471432+00:00
-- url     : https://prove2.me/theorems/0868459a-5c93-4112-aa53-a3963fbb7b18
-- title:
--   Lemma 4.3 — $\mathbb E\{m^{\ell,+}(B)-m^{\ell,0}(B)\}\le M/\ell$
-- statement:
--   Let $T$ be a conditionally independent infinite tree with average offspring numbers bounded by $\Delta$. For $B_{\min}>0$ and finite $\beta_{\max}$ and $\Delta$ there exists $M=M(\beta_{\max},B_{\min},\Delta)$ such that for every such tree, every $0\le\beta\le\beta_{\max}$, every field with $B_i\ge B_{\min}$ on $T(\ell)$, and every $\ell\ge1$,
--   $$\mathbb E\{m^{\ell,+}(\underline B)-m^{\ell,0}(\underline B)\}\le\frac{M}{\ell},$$
--   where $m^{\ell,+/0}(\underline B)=\langle\mu^{\ell,+/0},x_\varnothing\rangle$ are the root magnetizations under plus and free boundary conditions on $T(\ell)$.
--
--   The effect of the boundary condition on the root decays, uniformly over the tree law.
--
--   **Formalization Note** The conditions $0\le\beta\le\beta_{\max}$, $B_i\ge B_{\min}$ and $\ell\ge1$ come from Theorem 4.2's preamble and the proof. The upper bound $B_{\max}$ in the lemma's sentence plays no role and is omitted. $M$ is chosen before the tree law, $\beta$, the field and $\ell$. The field is nonrandom. Measurability of the integrand is part of the conclusion.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 12, Lemma 4.3, (4.5); p. 11, Theorem 4.2 (standing hypotheses)

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_CondIndepTree

namespace IsingLTL.FreeEntropy

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
    ∃ M : ℝ, ∀ (μ : Measure (List ℕ → ℕ)) [IsProbabilityMeasure μ], IsCondIndepTree μ Δ →
      ∀ (β : ℝ) (B : List ℕ → ℝ) (ℓ : ℕ), 0 ≤ β → β ≤ βmax → 1 ≤ ℓ →
        (∀ w : List ℕ, w.length ≤ ℓ → Bmin ≤ B w) →
        Measurable (fun ω => rootMag ω β B ℓ true - rootMag ω β B ℓ false) ∧
          ∫ ω, (rootMag ω β B ℓ true - rootMag ω β B ℓ false) ∂μ ≤ M / ℓ := by sorry

end IsingLTL.FreeEntropy
