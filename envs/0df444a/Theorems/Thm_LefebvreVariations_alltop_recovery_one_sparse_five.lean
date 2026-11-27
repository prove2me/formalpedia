-- Prove2me | Theorems.Thm_LefebvreVariations_alltop_recovery_one_sparse_five
-- name    : LefebvreVariations.alltop_recovery_one_sparse_five
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:22:42.576274+00:00
-- url     : https://prove2.me/theorems/bad870f8-c88d-5f88-b4fb-d1eff3cfe8da
-- title:
--   Lefebvre's variations, No. 263 — on a theme by Herman and Strohmer: basis pursuit and matching pursuit recover one target from the Alltop Gabor dictionary of order 5
-- statement:
--   Let $\Phi\in\mathbb{C}^{5\times25}$ be the Gabor dictionary of the Alltop sequence $f_n=5^{-1/2}e^{2\pi i n^3/5}$, with columns $H_if$ for the $25$ time-frequency shifts $H_i=M^{i\bmod 5}T^{\lfloor i/5\rfloor}$. For every $s\in\mathbb{C}^{25}$ with at most one nonzero entry, put $y=\Phi s=\bigl(\sum_i s_iH_i\bigr)f$. Then:
--
--   1. $s$ is the **unique** solution of basis pursuit
--   $$
--   \min\ \|s'\|_1\quad\text{subject to}\quad \Phi s'=y ;
--   $$
--   2. orthogonal matching pursuit, run for $\|s\|_0$ steps with any choice among ties at each step, returns exactly $s$.
--
--   This is the radar-recovery guarantee of Herman and Strohmer for $K<\tfrac12(\sqrt N+1)$ at the smallest admissible prime $N=5$, where it reads $K=1<1.618\ldots$: a single target (one time shift and one Doppler shift) is recovered exactly from $5$ samples of the received signal. It follows from the coherence criterion $K<\tfrac12(\mu^{-1}+1)$ with $\mu=1/\sqrt5$, which here reads $2\mu<1+\mu$, that is $\mu<1$.
--
--   **Formalization Note** The statement is `CompressedSensingRadar.matrix_recovery_guaranteed` with `N := 5` and `K := 1`, in the platform definitions `gaborDict`, `alltop`, `tfSynth`, `IsSparse`, `BPRecovers` and `OMPRecovers`. `IsSparse 1 s` means at most one nonzero entry, so `s = 0` is included. `BPRecovers` says that `s'` solves basis pursuit if and only if `s' = s`; `OMPRecovers` says that every run of `‖s‖₀` steps of `IsOMPRun` ends at `s`. The hypothesis `K < (√N + 1)/2` of the parent is `1 < (√5 + 1)/2`.
--
--   **Why this is a variation.** This varies the open platform problem CompressedSensingRadar.matrix_recovery_guaranteed (basis pursuit and OMP recover every K-sparse target vector from the Alltop Gabor dictionary when K < (sqrt N + 1)/2, N prime >= 5). It is the first admissible size, N = 5 and K = 1, in the parent's own definitions; it reduces to the coherence of the 5 x 25 dictionary being below 1, and is a model for K = 2 at N = 11.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   M. A. Herman and T. Strohmer, High-resolution radar via compressed sensing, IEEE Trans. Signal Process. 57 (2009), Theorem 1; J. A. Tropp, Greed is good: algorithmic results for sparse approximation, IEEE Trans. Inform. Theory 50 (2004); D. L. Donoho and M. Elad, Optimally sparse representation in general (nonorthogonal) dictionaries via l1 minimization, PNAS 100 (2003); all cited from memory, theorem numbers not verified. The Alltop dictionary has coherence 1/sqrt(5) = 0.4472 (checked numerically, numpy, matrices built as in the platform definitions), and the coherence condition 2K mu < 1 + mu holds for K = 1. Additionally the exact recovery condition max over atoms psi outside the support of the l1 norm of the pseudo-inverse of the support sub-dictionary applied to psi was computed over all supports and equals 0.447 < 1 (numpy, float64).

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic

set_option autoImplicit false

open CompressedSensingRadar

namespace LefebvreVariations

/-- **Radar recovery of a single target, `N = 5`.** Let `Φ` be the `5 × 25` Gabor dictionary of the Alltop
sequence of length `5`. For every `s ∈ ℂ^{25}` with at most one nonzero coefficient, basis pursuit
`min ‖s'‖₁ s.t. Φ s' = Φ s` has `s` as its unique solution, and orthogonal matching pursuit run for `‖s‖₀` steps
returns `s`, whatever the tie-breaking. This is the case `N = 5`, `K = 1 < (√5 + 1)/2` of the guarantee
`K < ½(√N + 1)` of Herman and Strohmer, *High-resolution radar via compressed sensing*, IEEE Trans. Signal Process.
57 (2009), Theorem 1, which rests on the coherence criterion `K < ½(μ⁻¹ + 1)` of Tropp (2004) and Donoho–Elad (2003)
(all cited from memory; theorem numbers not verified) and on `μ = 1/√N` for the Alltop dictionary.

**Formalization Note.** Same `gaborDict`, `alltop`, `tfSynth`, `IsSparse`, `BPRecovers` and `OMPRecovers` as
`CompressedSensingRadar.matrix_recovery_guaranteed`, at `N = 5` and `K = 1` (the hypothesis `K < (√5 + 1)/2` is
`1 < 1.618…`). The zero vector is included (`‖s‖₀ = 0`). -/
theorem alltop_recovery_one_sparse_five (s : Fin (5 ^ 2) → ℂ) (hs : IsSparse 1 s) :
    BPRecovers (gaborDict 5 (alltop 5)) ((tfSynth 5 s).mulVec (alltop 5)) s ∧
    OMPRecovers (gaborDict 5 (alltop 5)) ((tfSynth 5 s).mulVec (alltop 5)) s := by
  sorry

end LefebvreVariations
