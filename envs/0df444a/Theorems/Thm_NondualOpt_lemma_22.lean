-- Prove2me | Theorems.Thm_NondualOpt_lemma_22
-- name    : NondualOpt.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:43.852089+00:00
-- url     : https://prove2.me/theorems/18d1d62e-2214-4cbd-976c-83bee75c3002
-- title:
--   Lemma 22 — affine offsets do not increase the sequential entropy
-- statement:
--   Suppose $\Lambda_{X,H}=1$ (the standing assumption of §C.1). For every $n\ge1$ and every $0<\alpha\le1$,
--   $$
--   \log N^{\mathrm{seq}}_\infty\big(\alpha,\Phi\circ(\tfrac12A_{X,H}),n\big)\le\log N^{\mathrm{seq}}_\infty\big(\alpha/4,L_{X,H},n\big)+\frac{17\log5}\alpha .
--   $$
--   The offset coordinate and the envelopes $\phi\in\Phi$ cost only an additive $O(1/\alpha)$ in entropy, so the affine game is controlled by the linear class $L_{X,H}$.
--
--   Differences from the source:
--   - generalization: Λ_{X,H} = 1 → |⟨g, u⟩| ≤ 1 for g ∈ H, u ∈ X; offset class on H × [−1, 1]; reason: the proof uses only this bound and b ∈ [−1, 1]
--   - generalization: E a real Banach space, H ⊆ E∗ bounded with the duality pairing, X closed and bounded with 0 ∈ X (§2 standing setting) → real vector spaces E, F with an abstract bilinear pairing, Λ_{X,H} < ∞, no closedness or boundedness of X and no 0 ∈ X; reason: the proofs use H only through pairings ⟨g, u⟩ and the bound Λ_{X,H} (footnote 7); the duality pairing between E∗ and E with bounded H is the instance F = E∗
--   - encoding: log N → natural logarithm in [0, ∞] with log ∞ = ∞; reason: covering numbers may be infinite
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Lemma 22, p.30 (standing assumption Λ_{X,H} = 1 of §C.1, p.30)

import Mathlib
import Definitions.Def_NondualOpt_linClass
import Definitions.Def_NondualOpt_offsetClass
import Definitions.Def_NondualOpt_seqCoverNum
import Definitions.Def_NondualOpt_logN

open scoped ENNReal

namespace NondualOpt

/-- **Lemma 22 (Affine offsets do not increase the sequential entropy).** With `Λ_{X,H} = 1`, for
every `n ≥ 1` and every `0 < α ≤ 1`,
`log N^seq_∞(α, Φ∘(½A_{X,H}), n) ≤ log N^seq_∞(α/4, L_{X,H}, n) + 17 log 5 / α`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Lemma 22, p.30, under the standing
assumption of §C.1 ("Throughout this section, for simplicity, we assume that `Λ_{X,H} = 1`").

**Formalization Note.** `Λ_{X,H} = 1` is generalized to `|⟨g, u⟩| ≤ 1` on `H × X`, the only property
the proof uses; the offset class lives on `H × [−1, 1]`, the linear class on `H`. Logarithms of
covering numbers are in `ℝ≥0∞` (`logN`, `log ∞ = ∞`). -/
theorem lemma_22 {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (X : Set E) (H : Set F)
    (hΛ : ∀ g ∈ H, ∀ u ∈ X, |pair g u| ≤ 1) (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) :
    logN (seqCoverNum (offsetClass pair X H) α n) ≤
      logN (seqCoverNum (linClass pair X H) (α / 4) n) + ENNReal.ofReal (17 * Real.log 5 / α) := by sorry

end NondualOpt
