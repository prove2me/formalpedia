-- Prove2me | Theorems.Thm_LowErrExt_theorem_1_1
-- name    : LowErrExt.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:50.073832+00:00
-- url     : https://prove2.me/theorems/77b490a2-63af-4624-ac9d-03c300107072
-- title:
--   Theorem 1.1 — explicit two-source extractor for min-entropy $Cn^{1-c}$ with error $2^{-cn^c}$ and output length $m=k$
-- statement:
--   There are universal constants $C,c>0$ and an explicit function $\mathrm{2Ext}$ such that for every $n$, with
--   $$k=Cn^{1-c},\qquad m=\lceil k\rceil,\qquad \varepsilon=2^{-cn^{c}},$$
--   $\mathrm{2Ext}:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}^m$ is a two-source extractor for min-entropy $k$ with error $\varepsilon$: for all independent sources $\mathbf X,\mathbf Y$ on $\{0,1\}^n$ with $H_\infty[\mathbf X]\ge k$ and $H_\infty[\mathbf Y]\ge k$, the output $\mathrm{2Ext}(\mathbf X,\mathbf Y)$ is $\varepsilon$-close to $U_m$ in statistical distance.
--
--   This is the first explicit two-source extractor for min-entropy $o(n)$ with error $n^{-\omega(1)}$.
--
--   Differences from the source:
--   - reading: explicit (undefined in the paper) → computed by one deterministic polynomial-time Turing machine (Mathlib TM2) on all inputs, chosen after the constants; reason: the standard meaning in the area; a per-n family would make the word empty, since such functions exist by counting
--   - encoding: min-entropy k = Cn^{1−c} and output length m = k → real threshold k = Cn^{1−c} and m = ⌈k⌉; reason: k need not be an integer; ⌈k⌉ bits with threshold k is the strongest rounding on both sides
--   - encoding: 2Ext : {0,1}^n × {0,1}^n → {0,1}^m → one function on pairs of bit lists, output exactly m bits on n-bit inputs; reason: one function for all n, as explicitness requires
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 1.1, p.5 (= Theorem 5.1, p.34)

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_LowErrExt_IsTwoSourceExtList

namespace LowErrExt

/-- **Theorem 1.1 (Low-error two-source extractor).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 1.1, p.5 (restated as Theorem 5.1, p.34): "There is an explicit construction of a two-source
extractor 2Ext : {0, 1}n × {0, 1}n → {0, 1}m for min-entropy k = Cn^{1−c}, which has error ε = 2^{−cn^c}
and output length m = k, where C, c > 0 are universal constants."

**Formalization Note.** `C, c > 0` are real and chosen first; then one polynomial-time machine `F`
(`IsPolyTime`) gives `2Ext(x, y) = F [x, y]` for every `n`. For every `n`, on `n`-bit inputs it
outputs exactly `⌈Cn^{1−c}⌉` bits, and for all independent sources `X, Y` on `{0,1}ⁿ` with
min-entropy at least `Cn^{1−c}` the output is `2^{−cn^c}`-close to uniform. The real threshold
`k = Cn^{1−c}` and output length `⌈k⌉` are the strongest rounding on both sides. There is no
"large `n`" clause: when `Cn^{1−c} > n` no source qualifies (min-entropy is at most `n`), so only the
length clause binds. -/
theorem theorem_1_1 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∃ F : List (List Bool) → List Bool, IsPolyTime F ∧
        ∀ n : ℕ,
          IsTwoSourceExtList n (C * (n : ℝ) ^ (1 - c)) ⌈C * (n : ℝ) ^ (1 - c)⌉₊
            ((2 : ℝ) ^ (-(c * (n : ℝ) ^ c))) (fun x y => F [x, y]) := by sorry

end LowErrExt
