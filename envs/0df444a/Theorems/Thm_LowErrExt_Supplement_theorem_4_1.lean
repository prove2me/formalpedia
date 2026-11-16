-- Prove2me | Theorems.Thm_LowErrExt_Supplement_theorem_4_1
-- name    : LowErrExt.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:35:52.512742+00:00
-- url     : https://prove2.me/theorems/2349c38c-d3ff-457d-bd07-f59d0f42a9ae
-- title:
--   Theorem 4.1 — explicit affine extractor for min-entropy $n^{4/5+\alpha}$ with error $2^{-n^{\Omega_\alpha(1)}}$ and output $m=k-o(k)$
-- statement:
--   For every $\alpha>0$ there are a constant $c=c(\alpha)>0$, an explicit function $\mathrm{Ext}:\{0,1\}^n\to\{0,1\}^{m(n)}$ and output lengths $m(n)$ with
--   $$\frac{m(n)}{n^{4/5+\alpha}}\longrightarrow1\qquad(n\to\infty),$$
--   such that for every $n$ and every affine source $\mathbf X$ on $\mathbb F_2^n$ with $H_\infty[\mathbf X]\ge n^{4/5+\alpha}$,
--   $$\mathrm{SD}\big(\mathrm{Ext}(\mathbf X),U_{m(n)}\big)\le2^{-n^{c}}.$$
--
--   This is the paper's low-error affine extractor (Theorem 1.2): min-entropy $n^{1-\Omega(1)}$ with error $n^{-\omega(1)}$, improving on Bourgain's construction.
--
--   **Formalization Note** Explicit means one polynomial-time machine (`IsPolyTime`) for all $n$, with outputs of length exactly $m(n)$; the extractor property is `IsAffineExtractor`.
--
--   Differences from the source:
--   - encoding: error ε = 2^{−n^{Ω_α(1)}} → ∃ c > 0 (depending on α), error 2^{−n^c} for every n; reason: the meaning of Ω_α(1); stating it for every n loses nothing, since m(n) may be 0 for finitely many n (then the distance is 0)
--   - encoding: output length m = k − o(k), k = n^{4/5+α} → m : ℕ → ℕ with m(n)/n^{4/5+α} → 1; reason: k − m = o(k) iff m/k → 1
--   - encoding: explicit Ext → one polynomial-time machine F (IsPolyTime) for all n, outputs of length exactly m(n), read by machineBits; reason: the base mission's reading of explicit
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 4.1, p.29 (= Theorem 1.2, p.6)

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_LowErrExt_seededOfMachine
import Definitions.Def_LowErrExt_Supplement_machineBits
import Definitions.Def_LowErrExt_Supplement_IsAffineExtractor

namespace LowErrExt.Supplement

open LowErrExt Filter Topology

/-- **Theorem 4.1 (Low-error affine extractor — Theorem 1.2, restated).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 4.1, p.29 (= Theorem 1.2, p.6): "For every constant α > 0, there exists an explicit affine
extractor Ext : {0, 1}ⁿ → {0, 1}ᵐ for min-entropy n^{4/5+α}, which has error ε = 2^{−n^{Ω_α(1)}} and
output length m = k − o(k)."

**Formalization Note.** For each `α > 0`: `Ω_α(1)` is a constant `c > 0` depending on `α`; one
polynomial-time machine `F` (published `IsPolyTime`) computes `Ext` on every input length `n`, with
output length exactly `m(n)`; `m = k − o(k)` with `k = n^{4/5+α}` is `m(n)/k(n) → 1`. The extractor
property holds for every `n` (`IsAffineExtractor`, real threshold `n^{4/5+α}`, error `2^{−n^c}`);
this loses nothing against "for large `n`", since `m(n)` may be `0` for finitely many `n`. -/
theorem theorem_4_1 :
    ∀ α : ℝ, 0 < α →
      ∃ c : ℝ, 0 < c ∧
        ∃ F : List (List Bool) → List Bool, IsPolyTime F ∧
          ∃ m : ℕ → ℕ,
            Tendsto (fun n : ℕ => (m n : ℝ) / (n : ℝ) ^ ((4 : ℝ) / 5 + α)) atTop (𝓝 1) ∧
            ∀ n : ℕ,
              (∀ x : Fin n → ZMod 2, (F [bitsOf x]).length = m n) ∧
              IsAffineExtractor ((n : ℝ) ^ ((4 : ℝ) / 5 + α)) ((2 : ℝ) ^ (-((n : ℝ) ^ c)))
                (machineBits F (n := n) (m n)) := by sorry

end LowErrExt.Supplement
