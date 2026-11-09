-- Prove2me | Theorems.Thm_LinfContractionFP_lemma_2
-- name    : LinfContractionFP.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:20:37.027008+00:00
-- url     : https://prove2.me/theorems/ab55f766-df3e-44ba-8ece-c888c16861c4
-- title:
--   Lemma 2 — ThinLabel returns an $\eta$-approximate fixed point or a $\gamma\eta/8$-accurate labeling
-- statement:
--   Let $0<\gamma\le1$, $f$ a $(1-\gamma)$-contraction of $[0,1]^d$ with fixed point $x^*$. For any possibly degenerate box $[L,U]$ and $\eta>0$, ThinLabel$(L,U;\eta)$ returns either an $\eta$-approximate fixed point in $[0,1]^d$ or a
--   $$\frac{\gamma\eta}{8}\text{-accurate labeling of }[L,U],$$
--   provided its recursive calls of Solve return $\gamma\eta/2$-near fixed points of the restricted maps.
--
--   ThinLabel is the weak labeler that Amplify boosts.
--
--   Differences from the source:
--   - generalization: the recursive calls of Solve inside ThinLabel → any procedure solveSub meeting SubSolverSpec (η'-near fixed points of (1−γ)-contractions of dimension ≤ d/2); reason: this is the paper's inductive hypothesis; Solve itself meets it, so the statement specializes to the paper's
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Lemma 2, p.8; Algorithm 2, p.9

import Mathlib
import Definitions.Def_LinfContractionFP_IsContraction
import Definitions.Def_LinfContractionFP_IsApproxFixed
import Definitions.Def_LinfContractionFP_IsAccurateLabeling
import Definitions.Def_LinfContractionFP_SubSolverSpec
import Definitions.Def_LinfContractionFP_thinLabel

namespace LinfContractionFP

/-- Lemma 2: for any possibly degenerate box `[L, U]` and `η > 0`, ThinLabel(L, U; η)
(Algorithm 2) returns either an `η`-approximate fixed point in `[0,1]^d` or a `γη/8`-accurate
labeling of `[L, U]`.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Lemma 2, p.8: "Lemma 2. For any possibly degenerate box [L, U] and η > 0,
ThinLabel(L, U; η) (Algorithm 2) returns either an η-approximate fixed point in [0, 1]^d or a
γη/8-accurate labeling of [L, U]."

**Formalization Note.** The recursive calls of Solve on lines 6–7 are any `solveSub` meeting
`SubSolverSpec` (returning `γη/2`-near fixed points of the restricted maps of dimension at most
`d/2`), the paper's inductive hypothesis. Accuracy is with respect to the fixed point `xs`. -/
theorem lemma_2 {ι : Type} [Fintype ι] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (f : (ι → ℝ) → (ι → ℝ)) (hf : IsContraction γ f) (xs : ι → ℝ) (hxs : xs ∈ unitCube ι)
    (hfix : f xs = xs) (solveSub : (S : Finset ι) → ((↥S → ℝ) → (↥S → ℝ)) → ℝ → (↥S → ℝ))
    (hsub : SubSolverSpec γ solveSub) (L U : ι → ℝ) (η : ℝ) (hη : 0 < η) :
    (∀ p, thinLabel γ f solveSub L U η = Sum.inl p → IsApproxFixed f η p) ∧
      (∀ ℓ, thinLabel γ f solveSub L U η = Sum.inr ℓ →
        IsAccurateLabeling (γ * η / 8) L U xs ℓ) := by sorry

end LinfContractionFP
