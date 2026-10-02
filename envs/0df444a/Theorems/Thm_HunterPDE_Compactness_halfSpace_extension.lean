-- Prove2me | Theorems.Thm_HunterPDE_Compactness_halfSpace_extension
-- name    : HunterPDE.Compactness.halfSpace_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:02:49.191651+00:00
-- url     : https://prove2.me/theorems/4d881484-d5d9-4f52-9873-74d01637e6d0
-- title:
--   Theorem 3.41 — bounded linear extension W^{1,p}(ℝⁿ₊) → W^{1,p}(ℝⁿ)
-- statement:
--   There is a bounded linear map $E : W^{1,p}(\mathbb{R}^n_+) \to W^{1,p}(\mathbb{R}^n)$ such that $Ef = f$ pointwise a.e. in $\mathbb{R}^n_+$ and, for some constant $C = C(n, p)$,
--   $$\|Ef\|_{W^{1,p}(\mathbb{R}^n)} \le C \, \|f\|_{W^{1,p}(\mathbb{R}^n_+)}.$$
--
--   Extension operators let results proved on all of $\mathbb{R}^n$ (density, embeddings, compactness) be transferred to the half-space, and through local flattening to smooth domains.
--
--   **Formalization Note.** The dimension is $n = m + 1$, and $p$ ranges over $1 \le p \le \infty$ (Definition 3.23's range; the page states no restriction). $E$ acts on functions $\mathbb{R}^n \to \mathbb{R}$. It is required to be linear up to a.e. equality on $W^{1,p}(\mathbb{R}^n_+)$, to map it into $W^{1,p}(\mathbb{R}^n)$, to agree with $f$ a.e. on $\mathbb{R}^n_+$, and to obey the norm bound. $C$ and $E$ depend only on $m$ and $p$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 71–72, Theorem 3.41

import Mathlib
import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace

open MeasureTheory
open scoped ENNReal NNReal

namespace HunterPDE.Compactness

/-- Theorem 3.41 of Hunter, *Notes on PDEs* (revised 6/18/2014), pp. 71–72: there is a bounded
linear map `E : W^{1,p}(ℝⁿ₊) → W^{1,p}(ℝⁿ)` such that `Ef = f` pointwise a.e. in `ℝⁿ₊` and, for
some constant `C = C(n, p)`, `‖Ef‖_{W^{1,p}(ℝⁿ)} ≤ C ‖f‖_{W^{1,p}(ℝⁿ₊)}`.
The dimension is `n = m + 1` and `1 ≤ p ≤ ∞` (the range of Definition 3.23). Functions are
`ℝⁿ → ℝ`, of which only the values on `ℝⁿ₊` matter for the input; `E` is linear up to a.e.
equality on `W^{1,p}(ℝⁿ₊)` (elements of Sobolev spaces are a.e.-classes), and `C` and `E` are
chosen after `m` and `p` only. -/
theorem halfSpace_extension (m : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    ∃ (C : ℝ≥0) (E : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin (m + 1)) → ℝ),
      (∀ f g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
        MemW 1 p (upperHalfSpace m) f → MemW 1 p (upperHalfSpace m) g → ∀ a b : ℝ,
          E (a • f + b • g) =ᵐ[volume] a • E f + b • E g) ∧
      ∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, MemW 1 p (upperHalfSpace m) f →
        MemW 1 p Set.univ (E f) ∧
        E f =ᵐ[volume.restrict (upperHalfSpace m)] f ∧
        sobolevNorm 1 p Set.univ (E f) ≤ (C : ℝ≥0∞) * sobolevNorm 1 p (upperHalfSpace m) f := by sorry

end HunterPDE.Compactness
