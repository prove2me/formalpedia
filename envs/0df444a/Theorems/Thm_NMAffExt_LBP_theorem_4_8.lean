-- Prove2me | Theorems.Thm_NMAffExt_LBP_theorem_4_8
-- name    : NMAffExt.LBP.theorem_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:29:50.148798+00:00
-- url     : https://prove2.me/theorems/2db56156-97fb-4cd4-a7ac-d6e25a12df13
-- title:
--   Theorem 4.8 — $(k,\delta)$ section decorrelation gives $\mathrm{Corr}(f,P)\le\sqrt{2s(\delta+2^{-(n-k)})}$ for weakly read-once programs
-- statement:
--   Let $1\le k<n$ and suppose $f:\mathbb F_2^n\to\mathbb F_2$ has $(k,\delta)$ section decorrelation. Then every weakly read-once linear branching program $P$ on $n$ bits with $s$ vertices satisfies
--   $$\mathrm{Corr}(f,P)=\Bigl|\mathbb E_{x\sim U_n}(-1)^{f(x)+P(x)}\Bigr|\le\sqrt{2s\bigl(\delta+2^{-(n-k)}\bigr)}.$$
--
--   The bound reduces average-case hardness for weakly read-once linear branching programs to a decorrelation property of $f$ alone; Theorem 4.11 instantiates it with non-malleable affine extractors.
--
--   Differences from the source: none.
-- source:
--   Xin Li, Yan Zhong, Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds, arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 58 (PDF 60), Theorem 4.8, eq. (4.5)

import Mathlib
import Definitions.Def_NMAffExt_LBP_Basic
import Definitions.Def_NMAffExt_LBP_Program
import Definitions.Def_NMAffExt_LBP_SectionDecorrelation

namespace NMAffExt.LBP

/-- **Theorem 4.8.** Let `1 ≤ k < n` and let `f : 𝔽₂ⁿ → 𝔽₂` have `(k, δ)` section decorrelation.
Every size-`s` weakly read-once linear branching program `P` satisfies
`Corr(f, P) ≤ √(2s(δ + 2^{−(n−k)}))`. -/
theorem theorem_4_8 (n k : ℕ) (δ : ℝ) (f : (Fin n → ZMod 2) → ZMod 2)
    (hk : 1 ≤ k) (hkn : k < n) (hf : HasSectionDecorrelation k δ f)
    (s : ℕ) (P : Program n s) (hP : P.IsWeaklyReadOnce) :
    corr f P.eval ≤ Real.sqrt (2 * s * (δ + (2 : ℝ) ^ (-((n : ℤ) - k)))) := by sorry

end NMAffExt.LBP
