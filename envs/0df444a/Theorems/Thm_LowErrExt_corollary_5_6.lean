-- Prove2me | Theorems.Thm_LowErrExt_corollary_5_6
-- name    : LowErrExt.corollary_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:42.639815+00:00
-- url     : https://prove2.me/theorems/9a8ff66c-8017-4b83-8ad8-3a91e46634d9
-- title:
--   Corollary 5.6 — explicit strong two-source extractors with output $m\ge cn^c$
-- statement:
--   There are universal constants $C,c>0$ and an explicit function $\mathrm{2Ext}$ such that for every $n$, $\mathrm{2Ext}:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}^{m}$ with $m=m(n)\ge cn^c$ is a strong two-source extractor, with respect to both sources, for min-entropy $Cn^{1-c}$ and error
--   $$\varepsilon=2^{-cn^{c}} :$$
--   for all independent $\mathbf X,\mathbf Y$ on $\{0,1\}^n$ with $H_\infty\ge Cn^{1-c}$, $(\mathrm{2Ext}(\mathbf X,\mathbf Y),\mathbf Y)\approx_\varepsilon(U_m,\mathbf Y)$ and $(\mathrm{2Ext}(\mathbf X,\mathbf Y),\mathbf X)\approx_\varepsilon(U_m,\mathbf X)$.
--
--   Differences from the source:
--   - reading: explicit (undefined in the paper) → computed by one deterministic polynomial-time Turing machine (Mathlib TM2) on all inputs, chosen after the constants; reason: the standard meaning in the area; a per-n family would make the word empty, since such functions exist by counting
--   - encoding: 2Ext : {0,1}^n × {0,1}^n → {0,1}^m → a function on pairs of bit lists whose output on n-bit inputs has exactly m(n) bits, read as Fin m → Bool; reason: one function for all n, as explicitness requires
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Corollary 5.6, p.37

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_LowErrExt_IsTwoSourceExtractor

namespace LowErrExt

/-- **Corollary 5.6 (explicit strong two-source extractors).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Corollary 5.6, p.37: "There exists an explicit strong two-source extractor
2Ext : {0, 1}n × {0, 1}n → {0, 1}m for min-entropy k ≥ Cn^{1−c} (with respect to both sources), which
has error ε = 2^{−cn^c} and output length m ≥ cn^c, where C, c > 0 are universal constants."

**Formalization Note.** One polynomial-time machine `F` (chosen after `C, c`) computes
`2Ext(x, y) = F [x, y]` for every `n`; its output on `n`-bit inputs has exactly `m(n) ≥ c·n^c` bits.
Strong with respect to both sources: `(2Ext(X, Y), Y) ≈ε (U_m, Y)` and `(2Ext(X, Y), X) ≈ε (U_m, X)`.
"For min-entropy `k ≥ Cn^{1−c}`" is the threshold `Cn^{1−c}`: every source with min-entropy at least
that qualifies. Holds for every `n`, with no "large `n`" clause. -/
theorem corollary_5_6 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∃ F : List (List Bool) → List Bool, IsPolyTime F ∧
        ∃ m : ℕ → ℕ, ∀ n : ℕ, c * (n : ℝ) ^ c ≤ m n ∧
          (∀ x y : Fin n → Bool, (F [List.ofFn x, List.ofFn y]).length = m n) ∧
          IsStrongTwoSourceExtractor (C * (n : ℝ) ^ (1 - c)) ((2 : ℝ) ^ (-(c * (n : ℝ) ^ c)))
            (fun x y : Fin n → Bool => listOut (m n) (F [List.ofFn x, List.ofFn y])) := by sorry

end LowErrExt
