-- Prove2me | Theorems.Thm_FourierEntropyApprox_Supplement_theorem_4_3
-- name    : FourierEntropyApprox.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:07:27.225873+00:00
-- url     : https://prove2.me/theorems/9e2822e4-ca83-45fc-bdb6-c47fadee1037
-- title:
--   Theorem 4.3 — $\mathbb H(\widehat f^2)=O(\min\{\mathrm{aUC}^{\oplus}_0(f),\mathrm{aUC}^{\oplus}_1(f)\})$
-- statement:
--   Let $f:\{-1,1\}^n\to\{-1,1\}$ be a Boolean function and, for $b\in\{0,1\}$, let $\mathrm{aUC}^{\oplus}_b(f)$ be its average unambiguous $b$-parity-certificate complexity. There is an absolute constant $K>0$ such that for every $n$ and every Boolean $f$,
--
--   $$\mathbb H(\widehat f^2)\le K\min\{\mathrm{aUC}^{\oplus}_0(f),\ \mathrm{aUC}^{\oplus}_1(f)\}.$$
--
--   So a partition of one output side into affine subspaces of small average codimension already bounds the Fourier entropy, without any certificate for the other side. Restricted to subcube partitions this covers unambiguous DNFs.
--
--   **Formalization Note** $\mathbb H(\widehat f^2)$ is `entropyFun f`; $\mathrm{aUC}^{\oplus}_b(f)$ is `aUCParity f b`, where side $b=0$ is $f^{-1}(1)$ and side $b=1$ is $f^{-1}(-1)$.
--
--   Differences from the source:
--   - encoding: $O(\cdot)$ with an unspecified constant → one constant $K>0$ chosen before $n$ and $f$; reason: the meaning of $O(\cdot)$ for a statement over all $n$ and all Boolean $f$, as in the published goal
--   - encoding: $f:\{-1,1\}^n\to\{-1,1\}$ → real-valued $f$ on Fin n → Bool with IsBoolean f (true = −1); reason: the base mission's published conventions; same functions
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), Theorem 4.3, p.18 (PDF p.18); aUC⊕_b defined pp.4, 11–12

import Mathlib
import Definitions.Def_FourierEntropyApprox_entropyFun
import Definitions.Def_FourierEntropyApprox_IsBoolean
import Definitions.Def_FourierEntropyApprox_Supplement_aUCParity

set_option autoImplicit false

namespace FourierEntropyApprox

namespace Supplement

/-- **Theorem 4.3.** M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), p.18:
"Let f : {−1, 1}ⁿ → {−1, 1} be a Boolean function. Then, ℍ(f̂²) = O(min{aUC⊕₀(f), aUC⊕₁(f)}), where for
b ∈ {0, 1}, aUC⊕_b(f) is the average unambiguous b-parity-certificate complexity of f."

There is an absolute constant `K > 0` such that for every `n` and every Boolean `f`,
`ℍ(f̂²) ≤ K · min{aUC⊕₀(f), aUC⊕₁(f)}`.

**Formalization Note.** `ℍ(f̂²)` is `entropyFun f`; `aUC⊕_b(f)` is `aUCParity f b` (pp.4, 11–12), whose
side `b = 0` is `f⁻¹(1)` and `b = 1` is `f⁻¹(−1)`, with cells arbitrary nonempty affine subspaces and cost
`∑ co-dim(C) 2^{−co-dim(C)}`. The `O(·)` is one constant `K` chosen before `n` and `f`. -/
theorem theorem_4_3 :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (f : Cube n → ℝ), IsBoolean f →
      entropyFun f ≤ K * min (aUCParity f 0) (aUCParity f 1) := by sorry

end Supplement

end FourierEntropyApprox
