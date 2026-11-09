-- Prove2me | Theorems.Thm_MaskingHardness_lemma_A_2
-- name    : MaskingHardness.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:52:18.163299+00:00
-- url     : https://prove2.me/theorems/7c890251-adae-481d-8fee-ce6b52f830f1
-- title:
--   Lemma A.2 — the indistinguishability constraint functionals $R,S$ are conjugates under $\langle\cdot,\cdot\rangle_{\mathcal D}$
-- statement:
--   Let $\mathcal X,\mathcal Y$ be finite, $\mathcal D$ a distribution over $\mathcal X\times\mathcal Y$, $\mathcal C=\{c_i\}$ a finite collection of functions $\mathcal X\to\mathbb R^k$ and $\varepsilon\ge0$. Let $R,S$ be the indistinguishability constraint functionals of Definition 3.1:
--
--   $$
--   R(a)=\inf_{\lambda}\ \varepsilon\|\lambda\|_1\ \text{ s.t. }\ \Pr\Bigl[a(x,y)=\sum_i\lambda_ic_i(x)\Bigr]=1,\qquad S(b)=\begin{cases}0&\text{if }|\mathbb E[\langle c(x),b(x,y)\rangle]|\le\varepsilon\ \forall c\in\mathcal C,\\-\infty&\text{otherwise.}\end{cases}
--   $$
--
--   Then:
--
--   1. $R$ and $S$ are convex–concave conjugates under the pairing $\langle a,b\rangle_{\mathcal D}=\mathbb E_{\mathcal D}[\langle a(x,y),b(x,y)\rangle]$;
--   2. $R(a_1)=R(a_2)$ whenever $a_1=a_2$ $\mathcal D$-almost surely;
--   3. $S(b_1)=S(b_2)$ whenever $b_1=b_2$ $\mathcal D$-almost surely.
--
--   Items 2 and 3 are the fourth technical condition of Theorem 3.3 (footnote 17), which the proof of the main theorem needs in order to apply Theorem 3.3 to $R,S$.
--
--   **Formalization Note** "Almost surely" is "at every $(x,y)$ with $\mathcal D(x,y)>0$". $\varepsilon=0$ is included.
--
--   Differences from the source:
--   - reading: R and S 'are conjugates' → convex–concave conjugates (Definition 2.6) under ⟨a, b⟩_D; reason: the proof on p.40 computes the Definition 2.6 conjugate of R, and the proof of Theorem 1.9 uses the lemma as condition (b) of Theorem 3.3
--   - generalization: the conjugacy of R and S → the conjugacy plus footnote 17's support condition for R and for S; reason: the first conjunct is the lemma; the added conjuncts are the fourth condition of Theorem 3.3 that the proof of Theorem 1.9 needs for R, S
--   - generalization: a finite set C ⊆ {X → ℝᵏ} → a finite indexed family c : ι → X → ℝᵏ, repetitions allowed; reason: the paper's set C is the family indexed by its own elements (ι = C, c = inclusion), so the statement specializes to the source's
--   - encoding: a distribution D over X × Y → weights D x y ≥ 0 summing to 1 (IsDist); expectations are the weighted finite sums; reason: finite sets; same distributions, zero-probability pairs allowed
--   - encoding: Pr[a(x, y) = c_λ(x)] = 1; R(a) = +∞ if a ∉ span(C) → ∀ x y, 0 < D x y → a x y = combo c λ x; R as sInf in EReal (empty infimum = ⊤); reason: same functional
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Lemma A.2, p.40 (PDF p.42), with Definition 3.1, p.20 (PDF p.22), and footnote 17, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_MaskingHardness_IsConvConcConjWith
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_pairD
import Definitions.Def_MaskingHardness_constraintR
import Definitions.Def_MaskingHardness_constraintS

namespace MaskingHardness

/-- **Lemma A.2** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*,
arXiv:2611.05296, held version sha256 31134e8d…3e8d, Lemma A.2, printed p.40 = PDF p.42, with
Definition 3.1, printed p.20 = PDF p.22, and footnote 17, printed p.21 = PDF p.23).

The indistinguishability constraint functionals `R, S` of Definition 3.1 (for finite `X, Y`, a
distribution `D` on `X × Y`, a finite collection `C ⊆ {X → ℝᵏ}` and `ε ≥ 0`) are convex–concave
conjugates under `⟨a, b⟩_D = E_D[⟨a(x, y), b(x, y)⟩]`, and both depend only on the values of
their argument at pairs `(x, y)` of positive probability (the condition of footnote 17).

**Formalization Note** `C` is an indexed family `c : ι → X → ℝᵏ`; the two support clauses are
the fourth technical condition of Theorem 3.3 (footnote 17), which the proof of Theorem 1.9
needs for `R, S`. -/
theorem lemma_A_2 {X Y ι : Type*} [Fintype X] [Fintype Y] [Fintype ι] {k : ℕ}
    (D : X → Y → ℝ) (hD : IsDist D) (c : ι → X → Fin k → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    IsConvConcConjWith (pairD D) (constraintR D c ε) (constraintS D c ε) ∧
    (∀ a₁ a₂ : X → Y → Fin k → ℝ, (∀ x y, 0 < D x y → a₁ x y = a₂ x y) →
      constraintR D c ε a₁ = constraintR D c ε a₂) ∧
    (∀ b₁ b₂ : X → Y → Fin k → ℝ, (∀ x y, 0 < D x y → b₁ x y = b₂ x y) →
      constraintS D c ε b₁ = constraintS D c ε b₂) := by sorry

end MaskingHardness
