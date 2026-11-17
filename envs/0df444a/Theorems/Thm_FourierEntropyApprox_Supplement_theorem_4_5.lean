-- Prove2me | Theorems.Thm_FourierEntropyApprox_Supplement_theorem_4_5
-- name    : FourierEntropyApprox.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:08:49.12723+00:00
-- url     : https://prove2.me/theorems/b4958389-6338-44b8-af9a-aea80c774c17
-- title:
--   Theorem 4.5 — $\mathbb H(\widehat f^2)=O(\min\{\mathrm{avgdeg}^{\oplus}_{cj}(f),\mathrm{avgdeg}^{\oplus}_{cj}(-f)\})$
-- statement:
--   Let $f:\{-1,1\}^n\to\{-1,1\}$ be a Boolean function and $\mathrm{avgdeg}^{\oplus}_{cj}(f)$ its average conical junta degree over affine subspaces. There is an absolute constant $K>0$ such that for every $n$ and every Boolean $f$,
--
--   $$\mathbb H(\widehat f^2)\le K\min\{\mathrm{avgdeg}^{\oplus}_{cj}(f),\ \mathrm{avgdeg}^{\oplus}_{cj}(-f)\}.$$
--
--   An unambiguous partition is a conical junta with disjoint cells and unit weights, so this generalizes Theorem 4.3. Representations must be exact: on the represented side the weights of the subspaces containing a point must sum to one.
--
--   **Formalization Note** $\mathbb H(\widehat f^2)$ is `entropyFun f`; $\mathrm{avgdeg}^{\oplus}_{cj}(f)$ is `avgdegCJ f`, and `avgdegCJ (-f)` minimizes over representations of $(1+f)/2$.
--
--   Differences from the source:
--   - encoding: $O(\cdot)$ with an unspecified constant → one constant $K>0$ chosen before $n$ and $f$; reason: the meaning of $O(\cdot)$ for a statement over all $n$ and all Boolean $f$, as in the published goal
--   - encoding: $f:\{-1,1\}^n\to\{-1,1\}$ → real-valued $f$ on Fin n → Bool with IsBoolean f (true = −1); reason: the base mission's published conventions; same functions
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), Theorem 4.5, p.20 (PDF p.20); avgdeg⊕_cj defined p.13 and pp.4–5

import Mathlib
import Definitions.Def_FourierEntropyApprox_entropyFun
import Definitions.Def_FourierEntropyApprox_IsBoolean
import Definitions.Def_FourierEntropyApprox_Supplement_avgdegCJ

set_option autoImplicit false

namespace FourierEntropyApprox

namespace Supplement

/-- **Theorem 4.5.** M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), p.20:
"Let f : {−1, 1}ⁿ → {−1, 1} be a Boolean function. Then, ℍ(f̂²) = O(min{avgdeg⊕_cj(f), avgdeg⊕_cj(−f)})."

There is an absolute constant `K > 0` such that for every `n` and every Boolean `f`,
`ℍ(f̂²) ≤ K · min{avgdeg⊕_cj(f), avgdeg⊕_cj(−f)}`.

**Formalization Note.** `ℍ(f̂²)` is `entropyFun f`; `avgdeg⊕_cj(f)` is `avgdegCJ f` (p.13): minimum of
`∑ wᵢ co-dim(Cᵢ) 2^{−co-dim(Cᵢ)}` over exact representations `(1 − f)/2 = ∑ wᵢ 1_{Cᵢ}`, `wᵢ ≥ 0`, `Cᵢ`
nonempty affine subspaces (overlaps allowed); `avgdegCJ (-f)` represents `(1 + f)/2`. The `O(·)` is one
constant `K` chosen before `n` and `f`. -/
theorem theorem_4_5 :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (f : Cube n → ℝ), IsBoolean f →
      entropyFun f ≤ K * min (avgdegCJ f) (avgdegCJ (-f)) := by sorry

end Supplement

end FourierEntropyApprox
