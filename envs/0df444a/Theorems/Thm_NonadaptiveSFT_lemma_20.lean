-- Prove2me | Theorems.Thm_NonadaptiveSFT_lemma_20
-- name    : NonadaptiveSFT.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:12.834021+00:00
-- url     : https://prove2.me/theorems/866a49dd-455a-4213-a62a-ae2b0a9f816b
-- title:
--   Lemma 20 — final coefficient estimation: $|\mathrm{supp}\,\widetilde X|<17s$ and $\|\widehat X-\widetilde X\|_\infty<\tau/2$ w.p. $1-\delta_{est}/8$
-- statement:
--   Under the standing assumptions of §6 with $\tau>0$, fix a least-squares sample in the event of Lemma 14 and a final support $S\subseteq\Omega$ containing every $f$ with $|\widehat X(f)|\ge T_{min}$. Then the output $\widetilde X$ of the final coefficient estimation of §6.3 satisfies
--
--   $$|\mathrm{supp}(\widetilde X)|<17s,\qquad\|\widehat X-\widetilde X\|_\infty<\frac\tau2$$
--
--   with probability at least $1-\delta_{est}/8=1-1/240$ over the final estimation sample of $r_cv_c$ independent uniform points.
--
--   Together with Corollary 17 it gives the coordinatewise guarantee of the recovery algorithm.
--
--   Differences from the source:
--   - generalization: a final support S produced by an execution of the support identification phase (conditional probability) → every S ⊆ Ω containing {f : |X̂(f)| ≥ τ/2}, with the sample U fixed in the event of Lemma 14; reason: the proof uses only these properties of S and U; a run's support is one such S
--   - reading: the event of Lemma 14 → LSGood; reason: as in Lemma 16
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Lemma 20, p.37 (PDF p.39); §6.3 and (43), p.37

import Mathlib
import Definitions.Def_NonadaptiveSFT_Recovery

namespace NonadaptiveSFT

/-- **Lemma 20** (Final coefficient estimation), p.37 (PDF p.39).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…); §6.3 and (43), p.37; standing assumptions of §6 (p.33).

Fix an execution of the support identification phase on which the event of Lemma 14 holds and the
loop ends without an abort, with final support `S ⊆ Ω` containing every `f` with `|X̂(f)| ≥ T_min`.
Conditional on these observations and decisions, the output `X̃` satisfies `|supp(X̃)| < 17s` and
`‖X̂ − X̃‖_∞ < τ/2` with probability at least `1 − δ_est/8` over the final coefficient estimation
sample.

**Formalization Note.** "This step is reached only when τ > 0, which we assume throughout this
subsection" (p.37): `τ > 0`. The conditioning fixes the least-squares sample `U` (in the event
`LSGood` of Lemma 14) and the final support `S`; the lemma is stated for **every** `S ⊆ Ω` containing
`{f : |X̂(f)| ≥ τ/2}`, not only for supports produced by a run. The probability is over the
`r_c·v_c` independent uniform points of the final sample (`sampleProb`), and `X̃` is
`NonadaptiveSFT.finalEstimate`. `δ_est/8 = 1/240`. -/
theorem lemma_20 (a d : ℕ) (ha : 1 ≤ a) (hd : 1 ≤ d) (s : ℕ) (hs : 2 ≤ s)
    (hsN : s < 2 ^ (a * d)) (τ : ℝ) (hτ : 0 < τ) (X : G a d → ℂ)
    (h33 : sigma (lexKey a d) s (hat X) ^ 2 ≤ s * τ ^ 2)
    (U : Fin (nls s) → G a d) (hU : LSGood X U s τ) (S : Finset (G a d))
    (hSΩ : S ⊆ Omega X τ) (hheavy : ∀ f, τ / 2 ≤ ‖hat X f‖ → f ∈ S) :
    1 - (1 / 30) / 8 ≤ sampleProb (rc s * vc s) (fun pts =>
      suppCard (finalEstimate X U s S pts) < 17 * s ∧
      linf (hat X - finalEstimate X U s S pts) < τ / 2) := by sorry

end NonadaptiveSFT
