-- Prove2me | Theorems.Thm_LowErrExt_Supplement_theorem_3_20
-- name    : LowErrExt.Supplement.theorem_3_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:35:13.367248+00:00
-- url     : https://prove2.me/theorems/96d4509a-4334-4673-b8f2-dc4b6fd1e105
-- title:
--   Theorem 3.20 — explicit quadratic $(1/2+\gamma)n$-rank extractor for affine sources with $m=(\gamma/2)n-4$
-- statement:
--   For every $\gamma>0$ there is an explicit function $\mathrm{Ext}:\mathbb F_2^n\to\mathbb F_2^m$, with
--   $$m=\Big\lceil\frac{\gamma}{2}n-4\Big\rceil_+,$$
--   that is quadratic (each output bit is an $\mathbb F_2$-polynomial of degree at most $2$ in the input bits) and is a $k$-rank extractor for affine sources with $k=(1/2+\gamma)n$: for every affine subspace $A\subseteq\mathbb F_2^n$ with $\log_2|A|\ge(1/2+\gamma)n$, the image $\mathrm{Ext}(A)$ has dimension $m$.
--
--   Explicit means that one polynomial-time machine computes $\mathrm{Ext}$ on every input length $n$, with exactly $m$ output bits. Quadratic rank extractors of this kind feed the regularity lemma for quadratics in the affine extractor.
--
--   **Formalization Note** "Quadratic" is the published `QuadExt.Main.IsQuadraticMap`; the rank-extractor property is `IsRankExtAffine`; $\lceil\cdot\rceil_+$ is $0$ on negative reals.
--
--   Differences from the source:
--   - reading: m = (γ/2)n − 4 (not an integer in general, negative for small n) → m = ⌈(γ/2)n − 4⌉₊ output bits; reason: the stronger of the integral readings: truncating outputs keeps full dimension, so it implies the floor reading; the paper's IP construction meets it (Observation 3.19 with Remark 2.30 needs m < γn − 3, and ⌈(γ/2)n − 4⌉ ≤ (γ/2)n − 3)
--   - encoding: explicit Ext : F₂ⁿ → F₂ᵐ → one polynomial-time machine F (IsPolyTime) for all n, outputs of length exactly m, read by machineVec; reason: the base mission's reading of explicit (one uniform machine)
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 3.20, p.26 (definitions: Definition 3.17 and Remark 3.18, p.25)

import Mathlib
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_LowErrExt_seededOfMachine
import Definitions.Def_LowErrExt_Supplement_machineBits
import Definitions.Def_LowErrExt_Supplement_IsRankExtAffine

namespace LowErrExt.Supplement

open LowErrExt

/-- **Theorem 3.20 (Explicit quadratic rank extractor for affine sources).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 3.20, p.26: "There exists an explicit quadratic Ext : F₂ⁿ → F₂ᵐ that is a k-rank extractor
for affine sources, where k = (1/2 + γ)n for any γ > 0, and m = (γ/2)n − 4."

**Formalization Note.** For each `γ > 0` there is one polynomial-time machine `F` (published
`IsPolyTime`, "explicit") computing `Ext` on every input length `n`; on input `x` it outputs exactly
`m = ⌈(γ/2)n − 4⌉₊` bits (`⌈·⌉₊` is `0` on negative reals). Quadratic (Remark 3.18, p.25: each output
bit is an `𝔽₂`-polynomial of degree at most two) is the published `QuadExt.Main.IsQuadraticMap`.
The rank-extractor property is Definition 3.17 (`IsRankExtAffine`). -/
theorem theorem_3_20 :
    ∀ γ : ℝ, 0 < γ →
      ∃ F : List (List Bool) → List Bool, IsPolyTime F ∧
        ∀ n : ℕ,
          (∀ x : Fin n → ZMod 2, (F [bitsOf x]).length = ⌈γ / 2 * (n : ℝ) - 4⌉₊) ∧
          QuadExt.Main.IsQuadraticMap
            (machineVec F (n := n) ⌈γ / 2 * (n : ℝ) - 4⌉₊) ∧
          IsRankExtAffine ((1 / 2 + γ) * (n : ℝ))
            (machineVec F (n := n) ⌈γ / 2 * (n : ℝ) - 4⌉₊) := by sorry

end LowErrExt.Supplement
