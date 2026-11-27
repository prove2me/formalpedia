-- Prove2me | Theorems.Thm_LefebvreVariations_super_resolution_discrete_single_spike
-- name    : LefebvreVariations.super_resolution_discrete_single_spike
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:24:36.593182+00:00
-- url     : https://prove2.me/theorems/c14f2dcf-6d55-4525-9aaf-120dea04346e
-- title:
--   Lefebvre's variations, No. 268 — on a theme by Candès and Fernandez-Granda: a single spike is the unique l1 minimizer of its low-frequency Fourier data
-- statement:
--   Let $f_c\ge128$ and $N$ be natural numbers, and let $x\in\mathbb{C}^N$ have at most one nonzero entry. If $x'\in\mathbb{C}^N$ has the same low-frequency discrete Fourier data as $x$,
--   $$
--   \sum_{t=0}^{N-1}x'_t\,e^{-2\pi i kt/N}\;=\;\sum_{t=0}^{N-1}x_t\,e^{-2\pi i kt/N}\qquad\text{for all integers }|k|\le f_c ,
--   $$
--   and $x'\ne x$, then
--   $$
--   \|x\|_1\;=\;\sum_t|x_t|\;<\;\sum_t|x'_t|\;=\;\|x'\|_1 .
--   $$
--   In other words a single spike (or the zero signal) is the unique $\ell^1$-minimizer among all signals with the same low frequencies.
--
--   This is the one-spike case of the exact-recovery corollary for discrete super-resolution by $\ell^1$ minimization of Candès and Fernandez-Granda, where the minimum-separation hypothesis $\Delta\ge2/f_c$ on the support is empty. Only the frequencies $k=0$ and $k=1$ are needed: $\|x'\|_1\ge|\sum_tx'_t|$ with equality only if all entries of $x'$ have one common phase, and then $\bigl|\sum_tx'_te^{-2\pi it/N}\bigr|$ equals $\|x'\|_1$ only if $x'$ is supported at a single point.
--
--   **Formalization Note** The statement uses the platform definitions `partialFourier`, `l1norm` and `gridSupport` of `Def_SuperResolution_Basic`, as in `SuperResolution.discrete_exact_recovery`; the separation hypothesis of the parent is replaced by `(gridSupport x).card ≤ 1`. For `N ≤ 1` the data constraint at `k = 0` forces `x' = x`, so the statement is vacuous there. The condition `128 ≤ fc` is kept from the parent although the argument does not use it.
--
--   **Why this is a variation.** This varies the open platform problem SuperResolution.discrete_exact_recovery (exact recovery of a spike train with minimum separation 2/f_c by l1 minimization from the low frequencies |k| <= f_c, f_c >= 128). It is the one-spike case, where the separation condition is empty, stated with the parent's own definitions; it is the first size of the problem and can be proved from two Fourier coefficients.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   E. J. Candes and C. Fernandez-Granda, Towards a mathematical theory of super-resolution, Comm. Pure Appl. Math. 67 (2014) 906-956, Corollary 1.4 (cited from memory; page and corollary number not verified). The one-spike statement is elementary: the coefficients k = 0 and k = 1 and the equality case of the triangle inequality suffice, as sketched in the text.

import Mathlib
import Definitions.Def_SuperResolution_Basic

set_option autoImplicit false

open SuperResolution

namespace LefebvreVariations

/-- **Discrete super-resolution of a single spike.** Let `N, f_c` be natural numbers with `f_c ≥ 128`, and let
`x ∈ ℂ^N` have at most one nonzero entry. If `x' ∈ ℂ^N` has the same discrete Fourier coefficients as `x` for all
`|k| ≤ f_c`, `(F x')_k = ∑_t x'_t e^{-2πikt/N}`, and `x' ≠ x`, then `‖x‖₁ < ‖x'‖₁`. So a single spike is the unique
`ℓ¹`-minimizer of its low-frequency data. This is the one-spike case of Candès and Fernandez-Granda, *Towards a
mathematical theory of super-resolution*, Comm. Pure Appl. Math. 67 (2014), Corollary 1.4, where the minimum
separation `2/f_c` condition is empty (cited from memory; corollary number not verified). A direct argument uses only the
coefficients `k = 0` and `k = 1`: `‖x'‖₁ ≥ |(F x')_0| = ‖x‖₁`, and equality forces one common phase of the entries
of `x'` and then a single support point.

**Formalization Note.** Same `partialFourier`, `l1norm` and `gridSupport` as
`SuperResolution.discrete_exact_recovery`; the separation hypothesis is replaced by `(gridSupport x).card ≤ 1`
(the zero vector is allowed). For `N ≤ 1` the hypotheses `x' ≠ x` and the data constraint contradict each other. -/
theorem super_resolution_discrete_single_spike (N fc : ℕ) (hfc : 128 ≤ fc) (x : Fin N → ℂ)
    (hx : (gridSupport x).card ≤ 1) (x' : Fin N → ℂ)
    (hx' : ∀ k : ℤ, |k| ≤ fc → partialFourier x' k = partialFourier x k) (hne : x' ≠ x) :
    l1norm x < l1norm x' := by
  sorry

end LefebvreVariations
