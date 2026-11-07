-- Prove2me | Theorems.Thm_LowErrExt_theorem_5_2
-- name    : LowErrExt.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:03.281304+00:00
-- url     : https://prove2.me/theorems/c64c043d-487f-45c5-81e0-aae313188c0d
-- title:
--   Theorem 5.2 — regularity for bilinear maps on independent sources
-- statement:
--   There is a universal constant $C\ge1$ such that the following holds. Let $f:\mathbb F_2^n\times\mathbb F_2^n\to\mathbb F_2^t$ be bilinear, $\mathbf X$, $\mathbf Y$ independent sources on $\mathbb F_2^n$, and $\varepsilon\in(0,1]$. Then there is a product partition $\Gamma:\mathbb F_2^n\times\mathbb F_2^n\to\Sigma$ such that
--   $$\Pr_{\gamma\sim\Gamma(\mathbf X,\mathbf Y)}\big[f(\mathbf X,\mathbf Y)|_{\Gamma(\mathbf X,\mathbf Y)=\gamma}\text{ is an }\varepsilon\text{-biased affine source}\big]\ge1-\varepsilon,$$
--   where
--   $$H_0[\Sigma]\le\ell:=C\big(t^{C+1}n^{2C}\log(2/\varepsilon)\big)^{1/(2C+1)}+Ct .$$
--
--   This regularity lemma is what turns two independent sources into an almost affine source in the extractor construction (Lemma 5.3).
--
--   Differences from the source:
--   - encoding: f(X, Y)|Γ(X,Y)=γ with γ ∼ Γ(X, Y) → the law of f on the independent pair (X | A_γ, Y | B_γ), γ = Γ(x, y) for (x, y) ∼ (X, Y); reason: Γ is a product partition, so the fiber is A_γ × B_γ
--   - encoding: Σ → a finite type, H0[Σ] = log₂|Σ|; reason: H0[Σ] presupposes a finite set
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 5.2, p.34

import Mathlib
import Definitions.Def_LowErrExt_indepPair
import Definitions.Def_LowErrExt_condOn
import Definitions.Def_LowErrExt_bias
import Definitions.Def_LowErrExt_IsProductPartition
import Definitions.Def_LowErrExt_IsTwoSourceRankExt

namespace LowErrExt

/-- **Theorem 5.2 (Regularity for bilinear maps on independent sources).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 5.2, p.34: "Let f : Fn2 × Fn2 → Ft2 be a bilinear map, let X, Y ∼ Fn2 be independent sources,
and let ε ∈ (0, 1]. Then, there exists a product partition Γ : Fn2 × Fn2 → Σ such that
Pr_{γ∼Γ(X,Y)}[f(X, Y)|Γ(X,Y)=γ is an ε-biased affine source] ≥ 1 − ε, where
H0[Σ] ≤ ℓ := C(t^{C+1}n^{2C} log(2/ε))^{1/(2C+1)} + Ct for some universal constant C ≥ 1."

**Formalization Note.** `C` is chosen before `n, t, f` and the sources. `Σ` is a finite type and
`H0[Σ] = log₂|Σ|`. For `γ = Γ(x, y)` the law of `f(X, Y)|Γ(X,Y)=γ` is that of `f` on the
independent pair `(X | X ∈ fiberLeft Γ γ, Y | Y ∈ fiberRight Γ γ)`, since `Γ` is a product partition;
the probability is over `(x, y) ∼ (X, Y)`. -/
theorem theorem_5_2 :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n t : ℕ) (f : (Fin n → ZMod 2) × (Fin n → ZMod 2) → (Fin t → ZMod 2)),
        IsBilinear (fun x y => f (x, y)) →
          ∀ (X Y : PMF (Fin n → ZMod 2)) (ε : ℝ), 0 < ε → ε ≤ 1 →
            ∃ (Sig : Type) (_ : Fintype Sig) (Γ : (Fin n → ZMod 2) × (Fin n → ZMod 2) → Sig),
              IsProductPartition Γ ∧
              Real.logb 2 (Fintype.card Sig) ≤
                C * ((t : ℝ) ^ (C + 1) * (n : ℝ) ^ (2 * C) * Real.logb 2 (2 / ε)) ^ (1 / (2 * C + 1)) +
                  C * t ∧
              1 - ε ≤ probOf (indepPair X Y)
                {z | IsBiasedAffine ε ((indepPair (condOn X (fiberLeft Γ (Γ z)))
                      (condOn Y (fiberRight Γ (Γ z)))).map f)} := by sorry

end LowErrExt
