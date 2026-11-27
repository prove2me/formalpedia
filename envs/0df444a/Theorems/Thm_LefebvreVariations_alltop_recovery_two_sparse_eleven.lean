-- Prove2me | Theorems.Thm_LefebvreVariations_alltop_recovery_two_sparse_eleven
-- name    : LefebvreVariations.alltop_recovery_two_sparse_eleven
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:23:14.426585+00:00
-- url     : https://prove2.me/theorems/cf1fabdc-44dd-54d9-ac7c-f7ab80910974
-- title:
--   Lefebvre's variations, No. 264 — on a theme by Herman and Strohmer: basis pursuit and matching pursuit recover two targets from the Alltop Gabor dictionary of order 11
-- statement:
--   Let $\Phi\in\mathbb{C}^{11\times121}$ be the Gabor dictionary of the Alltop sequence $f_n=11^{-1/2}e^{2\pi i n^3/11}$, with columns $H_if$ for the $121$ time-frequency shifts $H_i=M^{i\bmod 11}T^{\lfloor i/11\rfloor}$. For every $s\in\mathbb{C}^{121}$ with at most two nonzero entries, put $y=\Phi s=\bigl(\sum_i s_iH_i\bigr)f$. Then:
--
--   1. $s$ is the **unique** solution of basis pursuit
--   $$
--   \min\ \|s'\|_1\quad\text{subject to}\quad \Phi s'=y ;
--   $$
--   2. orthogonal matching pursuit, run for $\|s\|_0$ steps with any choice among ties at each step, returns exactly $s$.
--
--   This is the radar-recovery guarantee of Herman and Strohmer for $K<\tfrac12(\sqrt N+1)$ at $N=11$, the first prime for which it allows $K=2$ targets: $\tfrac12(\sqrt{11}+1)=2.158\ldots$, while $N=5$ and $N=7$ only allow $K=1$. It follows from the coherence criterion $K<\tfrac12(\mu^{-1}+1)$ with $\mu=1/\sqrt{11}$, since $4\mu=1.206<1+\mu=1.301$.
--
--   **Formalization Note** The statement is `CompressedSensingRadar.matrix_recovery_guaranteed` with `N := 11` and `K := 2`, in the platform definitions `gaborDict`, `alltop`, `tfSynth`, `IsSparse`, `BPRecovers` and `OMPRecovers`. `IsSparse 2 s` means at most two nonzero entries, so supports of size $0$, $1$ and $2$ are all covered. `BPRecovers` says that `s'` solves basis pursuit if and only if `s' = s`; `OMPRecovers` says that every run of `‖s‖₀` steps of `IsOMPRun` ends at `s`.
--
--   **Why this is a variation.** This varies the open platform problem CompressedSensingRadar.matrix_recovery_guaranteed (basis pursuit and OMP recover every K-sparse target vector from the Alltop Gabor dictionary when K < (sqrt N + 1)/2, N prime >= 5). It is the first size where the guarantee covers K = 2 targets, N = 11, in the parent's own definitions; it follows from the coherence 1/sqrt(11) of the 11 x 121 dictionary and the coherence criterion K < (1/mu + 1)/2.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   M. A. Herman and T. Strohmer, High-resolution radar via compressed sensing, IEEE Trans. Signal Process. 57 (2009), Theorem 1; J. A. Tropp, Greed is good: algorithmic results for sparse approximation, IEEE Trans. Inform. Theory 50 (2004); D. L. Donoho and M. Elad, Optimally sparse representation in general (nonorthogonal) dictionaries via l1 minimization, PNAS 100 (2003); all cited from memory, theorem numbers not verified. The Alltop dictionary for N = 11 has coherence 0.30151134457776 = 1/sqrt(11) (checked numerically, numpy, matrices built as in the platform definitions), and 2K mu = 1.206 < 1 + mu = 1.301 for K = 2. Additionally the coherence was verified exactly (all 7260 atom pairs, arithmetic in Z[zeta_11]: modulus 0 or 1/sqrt(11)), and the exact recovery condition (max l1 norm of the pseudo-inverse of the support sub-dictionary applied to an outside atom) was computed over all 7260 two-element supports and is at most 0.8494 < 1 (numpy, float64).

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic

set_option autoImplicit false

open CompressedSensingRadar

namespace LefebvreVariations

/-- **Radar recovery of two targets, `N = 11`.** Let `Φ` be the `11 × 121` Gabor dictionary of the Alltop
sequence of length `11`. For every `s ∈ ℂ^{121}` with at most two nonzero coefficients, basis pursuit
`min ‖s'‖₁ s.t. Φ s' = Φ s` has `s` as its unique solution, and orthogonal matching pursuit run for `‖s‖₀` steps
returns `s`, whatever the tie-breaking. `N = 11` is the first prime for which the guarantee
`K < ½(√N + 1)` of Herman and Strohmer, *High-resolution radar via compressed sensing*, IEEE Trans. Signal Process.
57 (2009), Theorem 1, allows `K = 2` (`(√11 + 1)/2 = 2.158…`; for `N = 5, 7` only `K = 1`). It rests on the coherence
criterion `K < ½(μ⁻¹ + 1)` of Tropp (2004) and Donoho–Elad (2003) with `μ = 1/√11` (all cited from memory;
theorem numbers not verified; the coherence value was checked numerically).

**Formalization Note.** Same `gaborDict`, `alltop`, `tfSynth`, `IsSparse`, `BPRecovers` and `OMPRecovers` as
`CompressedSensingRadar.matrix_recovery_guaranteed`, at `N = 11` and `K = 2`. Supports of size `0`, `1` and `2`
are all covered. -/
theorem alltop_recovery_two_sparse_eleven (s : Fin (11 ^ 2) → ℂ) (hs : IsSparse 2 s) :
    BPRecovers (gaborDict 11 (alltop 11)) ((tfSynth 11 s).mulVec (alltop 11)) s ∧
    OMPRecovers (gaborDict 11 (alltop 11)) ((tfSynth 11 s).mulVec (alltop 11)) s := by
  sorry

end LefebvreVariations
