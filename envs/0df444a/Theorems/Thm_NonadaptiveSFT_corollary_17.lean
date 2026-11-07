-- Prove2me | Theorems.Thm_NonadaptiveSFT_corollary_17
-- name    : NonadaptiveSFT.corollary_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:39.282726+00:00
-- url     : https://prove2.me/theorems/2b5cfd65-123c-462d-90f5-cc8205f333d7
-- title:
--   Corollary 17 — successful support identification in fewer than $30838s$ rounds
-- statement:
--   Under the standing assumptions of §6, suppose the least-squares sample lies in the event of Lemma 14 and every call made by the algorithm succeeds. Then the algorithm terminates without aborting, and the loop ends after fewer than $30838s$ rounds. If $\tau>0$, the final support satisfies $S\subseteq\Omega$ and contains every $f$ with $|\widehat X(f)|\ge T_{min}$. If $\tau=0$, the algorithm returns $\widehat X$.
--
--   This is the correctness of the search phase; the final estimation then only has to refine the coefficients on $S$.
--
--   **Formalization Note** A call is made when its round is reached and passes the checks of step 2. The conclusion gives $n<30838s$ such that the state after round $n$ is the exit to the final estimation with such an $S$ (for $\tau>0$), or the return of $\widehat X$ (for $\tau=0$).
--
--   Differences from the source:
--   - generalization: the algorithm with its locator → the loop of §6.1 with an arbitrary sequence of locator outcomes; reason: the corollary uses only the success of every call made; the paper's locator is one such sequence
--   - reading: the event of Lemma 14 → LSGood: for every S ⊆ Ω, A_S^*A_S nonsingular and (28), (29); reason: as in Lemma 16
--   - encoding: terminates without aborting, and the loop ends after fewer than 30838s rounds → ∃ n < 30838s with the state after round n terminal and not aborted (exit to step 5, or return); reason: terminal states are fixed points
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Corollary 17, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_NonadaptiveSFT_Recovery

namespace NonadaptiveSFT

/-- **Corollary 17** (Successful support identification), p.35 (PDF p.37).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…); standing assumptions of §6 (p.33).

Suppose that the event of Lemma 14 holds and that every call made by the algorithm succeeds. Then
the algorithm terminates without aborting, and the loop ends after fewer than `30838s` rounds. If
`τ > 0`, the final support satisfies `S ⊆ Ω` and contains every `f` with `|X̂(f)| ≥ T_min`. If `τ = 0`,
the algorithm returns `X̂`.

**Formalization Note.** Same loop as Lemma 16, for an arbitrary locator outcome sequence `loc`;
"every call made succeeds" is: whenever call `i` is made (round `i` is reached and passes the
checks of step 2), call `i` succeeds. The conclusion gives
a round count `n < 30838s` after which the loop is in a terminal, non-aborted state: for `τ > 0` it has
left for step 5 with a support `S ⊆ Ω` containing every `f` with `|X̂(f)| ≥ τ/2`; for `τ = 0` it has
returned the vector `X̂`. Terminal states are fixed points, so the loop performs at most `n` rounds. -/
theorem corollary_17 (a d : ℕ) (ha : 1 ≤ a) (hd : 1 ≤ d) (s : ℕ) (hs : 2 ≤ s)
    (hsN : s < 2 ^ (a * d)) (τ : ℝ) (hτ : 0 ≤ τ) (X : G a d → ℂ)
    (h33 : sigma (lexKey a d) s (hat X) ^ 2 ≤ s * τ ^ 2)
    (U : Fin (nls s) → G a d) (hU : LSGood X U s τ) (loc : ℕ → Option (Finset (G a d)))
    (hall : ∀ i, CallMade X U s τ loc i → CallSucceeds X U s τ loc i) :
    ∃ n : ℕ, (n : ℝ) < 30838 * (s : ℝ) ∧
      (0 < τ → ∃ S : Finset (G a d), loopAt X U s τ loc n = .final S ∧ S ⊆ Omega X τ ∧
        ∀ f, τ / 2 ≤ ‖hat X f‖ → f ∈ S) ∧
      (τ = 0 → loopAt X U s τ loc n = .returned (hat X)) := by sorry

end NonadaptiveSFT
