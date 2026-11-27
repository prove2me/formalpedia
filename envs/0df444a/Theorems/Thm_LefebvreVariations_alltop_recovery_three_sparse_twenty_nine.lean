-- Prove2me | Theorems.Thm_LefebvreVariations_alltop_recovery_three_sparse_twenty_nine
-- name    : LefebvreVariations.alltop_recovery_three_sparse_twenty_nine
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:23:30.549932+00:00
-- url     : https://prove2.me/theorems/776060ec-9da7-55a7-ac82-191e53636306
-- title:
--   Lefebvre's variations, No. 265 — on a theme by Herman and Strohmer: basis pursuit and matching pursuit recover three targets from the Alltop Gabor dictionary of order 29
-- statement:
--   Let $\Phi\in\mathbb{C}^{29\times841}$ be the Gabor dictionary of the Alltop sequence $f_n=29^{-1/2}e^{2\pi i n^3/29}$, with columns $H_if$ for the $841$ time-frequency shifts $H_i=M^{i\bmod 29}T^{\lfloor i/29\rfloor}$. For every $s\in\mathbb{C}^{841}$ with at most three nonzero entries, put $y=\Phi s=\bigl(\sum_i s_iH_i\bigr)f$. Then:
--
--   1. $s$ is the **unique** solution of basis pursuit
--   $$
--   \min\ \|s'\|_1\quad\text{subject to}\quad \Phi s'=y ;
--   $$
--   2. orthogonal matching pursuit, run for $\|s\|_0$ steps with any choice among ties at each step, returns exactly $s$.
--
--   This is the radar-recovery guarantee of Herman and Strohmer for $K<\tfrac12(\sqrt N+1)$ at $N=29$, the first prime for which it allows $K=3$ targets: $\tfrac12(\sqrt{29}+1)=3.192\ldots$, while every prime $N\le23$ allows $K\le2$. It follows from the coherence criterion $K<\tfrac12(\mu^{-1}+1)$ with $\mu=1/\sqrt{29}$, since $6\mu=1.114<1+\mu=1.186$.
--
--   **Formalization Note** The statement is `CompressedSensingRadar.matrix_recovery_guaranteed` with `N := 29` and `K := 3`, in the platform definitions `gaborDict`, `alltop`, `tfSynth`, `IsSparse`, `BPRecovers` and `OMPRecovers`. `IsSparse 3 s` means at most three nonzero entries, so supports of size $0$ to $3$ are covered. `BPRecovers` says that `s'` solves basis pursuit if and only if `s' = s`; `OMPRecovers` says that every run of `‖s‖₀` steps of `IsOMPRun` ends at `s`.
--
--   **Why this is a variation.** This varies the open platform problem CompressedSensingRadar.matrix_recovery_guaranteed (basis pursuit and OMP recover every K-sparse target vector from the Alltop Gabor dictionary when K < (sqrt N + 1)/2, N prime >= 5). It is the first size where the guarantee covers K = 3 targets, N = 29, in the parent's own definitions; it follows from the coherence 1/sqrt(29) of the 29 x 841 dictionary and the coherence criterion K < (1/mu + 1)/2.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   M. A. Herman and T. Strohmer, High-resolution radar via compressed sensing, IEEE Trans. Signal Process. 57 (2009), Theorem 1; J. A. Tropp, Greed is good: algorithmic results for sparse approximation, IEEE Trans. Inform. Theory 50 (2004); D. L. Donoho and M. Elad, Optimally sparse representation in general (nonorthogonal) dictionaries via l1 minimization, PNAS 100 (2003); all cited from memory, theorem numbers not verified. The Alltop dictionary for N = 29 has coherence 0.18569533817711 = 1/sqrt(29) (checked numerically, numpy, matrices built as in the platform definitions), and 2K mu = 1.114 < 1 + mu = 1.186 for K = 3. Additionally the coherence was verified exactly (all 353220 atom pairs, arithmetic in Z[zeta_29]: modulus 0 or 1/sqrt(29)), and the exact recovery condition was computed over all three-element supports containing atom 0 (all supports up to the Heisenberg-group symmetry of the dictionary) and is at most 0.8862 < 1 (numpy, float64).

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic

set_option autoImplicit false

open CompressedSensingRadar

namespace LefebvreVariations

/-- **Radar recovery of three targets, `N = 29`.** Let `Φ` be the `29 × 841` Gabor dictionary of the Alltop
sequence of length `29`. For every `s ∈ ℂ^{841}` with at most three nonzero coefficients, basis pursuit
`min ‖s'‖₁ s.t. Φ s' = Φ s` has `s` as its unique solution, and orthogonal matching pursuit run for `‖s‖₀` steps
returns `s`, whatever the tie-breaking. `N = 29` is the first prime for which the guarantee
`K < ½(√N + 1)` of Herman and Strohmer, *High-resolution radar via compressed sensing*, IEEE Trans. Signal Process.
57 (2009), Theorem 1, allows `K = 3` (`(√29 + 1)/2 = 3.192…`; for `N ≤ 23` only `K ≤ 2`). It rests on the coherence
criterion `K < ½(μ⁻¹ + 1)` of Tropp (2004) and Donoho–Elad (2003) with `μ = 1/√29` (all cited from memory;
theorem numbers not verified; the coherence value was checked numerically).

**Formalization Note.** Same `gaborDict`, `alltop`, `tfSynth`, `IsSparse`, `BPRecovers` and `OMPRecovers` as
`CompressedSensingRadar.matrix_recovery_guaranteed`, at `N = 29` and `K = 3`. Supports of size `0` to `3` are
covered. -/
theorem alltop_recovery_three_sparse_twenty_nine (s : Fin (29 ^ 2) → ℂ) (hs : IsSparse 3 s) :
    BPRecovers (gaborDict 29 (alltop 29)) ((tfSynth 29 s).mulVec (alltop 29)) s ∧
    OMPRecovers (gaborDict 29 (alltop 29)) ((tfSynth 29 s).mulVec (alltop 29)) s := by
  sorry

end LefebvreVariations
