-- Prove2me | Theorems.Thm_LowErrExt_Supplement_theorem_4_2
-- name    : LowErrExt.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:36:27.896368+00:00
-- url     : https://prove2.me/theorems/df55688b-5eac-481a-9d89-93d4a0adf0f1
-- title:
--   Theorem 4.2 — regularity for quadratics on affine sources, $H_0[\Sigma]\le t\log(1/\varepsilon)+t$
-- statement:
--   Let $f:\mathbb F_2^n\to\mathbb F_2^t$ be quadratic, let $\mathbf X$ be an affine source on $\mathbb F_2^n$, and let $\varepsilon\in(0,1]$. Then there are a finite set $\Sigma$ and an affine partition $\Gamma:\mathbb F_2^n\to\Sigma$ with
--   $$H_0[\Sigma]=\log_2|\Sigma|\le t\log(1/\varepsilon)+t$$
--   such that, for every $\gamma$ with $\Pr[\Gamma(\mathbf X)=\gamma]>0$, the source $f(\mathbf X|_{\Gamma(\mathbf X)=\gamma})$ is an $\varepsilon$-biased affine source: every parity of it has bias $1$ or bias at most $\varepsilon$.
--
--   Fixing a little information about an affine source thus makes a quadratic map constant or unbiased in every direction; this is the first step of the affine extractor.
--
--   **Formalization Note** Quadratic is the published `QuadExt.Main.IsQuadraticMap`; $\varepsilon$-biased affine sources are the published `IsBiasedAffine` (Definition 3.28); "probability $1$ over $\gamma\sim\Gamma(\mathbf X)$" is stated for every $\gamma$ of positive probability.
--
--   Differences from the source:
--   - encoding: Pr_{γ∼Γ(X)}[f(X|Γ(X)=γ) is an ε-biased affine source] = 1 → for every γ with Pr[Γ(X) = γ] > 0, IsBiasedAffine ε (f(X|Γ⁻¹{γ})); reason: an event over a finite distribution has probability 1 iff it holds at every atom of positive mass
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 4.2, p.29

import Mathlib
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_LowErrExt_H2
import Definitions.Def_LowErrExt_condOn
import Definitions.Def_LowErrExt_bias
import Definitions.Def_LowErrExt_IsAffineSource
import Definitions.Def_LowErrExt_Supplement_IsAffinePartition

namespace LowErrExt.Supplement

open LowErrExt

/-- **Theorem 4.2 (Regularity for quadratics on affine sources).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 4.2, p.29: "Let f : F₂ⁿ → F₂ᵗ be a quadratic, let X ∼ F₂ⁿ be an affine source, and let
ε ∈ (0, 1]. Then, there exists an affine partition Γ : F₂ⁿ → Σ such that
Pr_{γ∼Γ(X)}[f(X|_{Γ(X)=γ}) is an ε-biased affine source] = 1, where H0[Σ] ≤ ℓ := t log(1/ε) + t."

**Formalization Note.** Quadratic ("each output bit is an F₂-polynomial of degree at most 2", p.29)
is the published `QuadExt.Main.IsQuadraticMap`; affine sources, `ε`-biased affine sources
(Definition 3.28) and `H0` are the published `IsAffineSource`, `IsBiasedAffine`, `H0`. `Σ` is a
finite type chosen existentially (`Sig`). "Probability `1` over `γ ∼ Γ(X)`" is: for every `γ` with
`Pr[Γ(X) = γ] > 0`. `X|_{Γ(X)=γ}` is `condOn X (Γ⁻¹{γ})`. Logarithms are base 2. -/
theorem theorem_4_2 {n t : ℕ} (f : (Fin n → ZMod 2) → (Fin t → ZMod 2))
    (hf : QuadExt.Main.IsQuadraticMap f) (X : PMF (Fin n → ZMod 2)) (hX : IsAffineSource X)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (Sig : Type) (_ : Fintype Sig) (Γ : (Fin n → ZMod 2) → Sig),
      IsAffinePartition Γ ∧
      H0 (Set.univ : Set Sig) ≤ (t : ℝ) * Real.logb 2 (1 / ε) + t ∧
      ∀ γ : Sig, 0 < probOf X (Γ ⁻¹' {γ}) →
        IsBiasedAffine ε ((condOn X (Γ ⁻¹' {γ})).map f) := by sorry

end LowErrExt.Supplement
