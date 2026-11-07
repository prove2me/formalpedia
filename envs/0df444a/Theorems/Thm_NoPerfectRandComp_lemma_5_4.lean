-- Prove2me | Theorems.Thm_NoPerfectRandComp_lemma_5_4
-- name    : NoPerfectRandComp.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:48:14.445914+00:00
-- url     : https://prove2.me/theorems/6d614348-d2a6-436a-b31e-ff7f18b87de9
-- title:
--   Lemma 5.4 — $\mathrm{LR}(\hat M_q)=\Theta(b_qq^2)$ and the saving is $O(\log q)$
-- statement:
--   There are absolute constants such that, for odd $q \ge 3$:
--   1. $\mathrm{LR}(\hat M_q) = \Theta(b_q q^2)$;
--   2. every nonconstant outer Boolean function $F$ (possibly partial, as in §2.1) satisfies
--   $$
--   \frac{\mathrm{R}(F)\,\mathrm{R}(\hat M_q)}{\mathrm{R}(F \circ \hat M_q)} = O(\log q) .
--   $$
--
--   The second clause gives the lower half of Theorem 5.1 and shows that no outer function obtains a larger saving with this inner family.
--
--   **Formalization Note** The constants are uniform in $q$, in the encoding and in $F$; the ratio bound is stated multiplied out, $\mathrm{R}(F)\mathrm{R}(\hat M_q) \le C\log_2 q\cdot \mathrm{R}(F\circ\hat M_q)$. $F$ ranges over possibly partial Boolean functions on any finite set of coordinates (the convention of §2.1), nonconstant meaning that $F$ takes both values on its domain; $F\circ\hat M_q$ is the partial block composition.
--
--   Differences from the source:
--   - generalization: the paper's fixed pointer-cell encoding → every admissible encoding; reason: the upper bound runs Lemma 5.3, the lower bound uses only the privacy of Lemma 4.5 and the surjective decoder
--   - encoding: Θ(b_q q²) and O(log q) → explicit constants 0 < c, C uniform in q, the encoding and F; the ratio multiplied out; reason: definition of Θ and O; R(F ∘ M̂_q) > 0 for nonconstant F, so the multiplied form is the ratio bound
--   - encoding: nonconstant outer Boolean function F → a PartialFn F on a finite coordinate type taking both values on its domain, composed by PartialFn.comp with the total M̂_q; reason: §2.1 lets f, g, h be possibly partial; for total F the domain of the composition is every input and its value is the block composition, so the total case is included
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Lemma 5.4, p.20

import Mathlib
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_LR
import Definitions.Def_NoPerfectRandComp_Mhat

namespace NoPerfectRandComp

/-- Lemma 5.4 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.20 (linearised cost of the inner function): for odd `q ≥ 3`,
`LR(M̂_q) = Θ(b_q q²)`; consequently every nonconstant outer Boolean function `F` satisfies
`R(F) R(M̂_q) / R(F ∘ M̂_q) = O(log q)`.

**Formalization Note** Both `Θ` and `O` are explicit constants, uniform in `q`, in the encoding
and in `F`. The ratio bound is stated multiplied out, `R(F) R(M̂_q) ≤ C log₂ q · R(F ∘ M̂_q)`.
`F` ranges over possibly partial Boolean functions on any finite coordinate type (the convention
of §2.1, p.4); nonconstant means that `F` takes both values on `Dom(F)`, and `F ∘ M̂_q` is the
partial block composition, whose domain is the set of inputs whose vector of `M̂_q`-values lies in
`Dom(F)`. For total `F` this is `R(F) R(M̂_q) ≤ C log₂ q · R(F ∘ M̂_q)` with ordinary block
composition. -/
theorem lemma_5_4 :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ q : ℕ, Odd q → 3 ≤ q →
      ∀ enc : Encoding (bq q) (PtrCell q),
        ENNReal.ofReal (c * bq q * q ^ 2) ≤ LR (PartialFn.total (Mhat q enc)) ∧
        LR (PartialFn.total (Mhat q enc)) ≤ ENNReal.ofReal (C * bq q * q ^ 2)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, Odd q → 3 ≤ q → ∀ enc : Encoding (bq q) (PtrCell q),
      ∀ (ι : Type) [Fintype ι] (F : PartialFn ι),
        (∃ x ∈ F.dom, ∃ y ∈ F.dom, F.val x ≠ F.val y) →
        (R F : ℝ) * Rt (Mhat q enc) ≤
          C * Real.logb 2 q * R (F.comp (PartialFn.total (Mhat q enc)))) := by sorry

end NoPerfectRandComp
