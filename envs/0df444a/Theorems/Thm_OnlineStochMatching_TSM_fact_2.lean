-- Prove2me | Theorems.Thm_OnlineStochMatching_TSM_fact_2
-- name    : OnlineStochMatching.TSM.fact_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:35:32.837973+00:00
-- url     : https://prove2.me/theorems/b581946e-624c-4e16-9fff-e698ec9fc4bd
-- title:
--   Fact 2 — the number of satisfied bin sequences is at least $\ell(1 - 2^{|R|}/e^c) - \varepsilon d n - O(\ell/n)$
-- statement:
--   Throw $n$ balls independently and uniformly into $n$ bins. Let $B_1, \dots, B_\ell$ be sequences of bins, each consisting of $c$ distinct bins $B_a = (b_1, \dots, b_c)$, such that no bin lies in more than $d$ of the sequences. Fix a set $R \subseteq \{1, \dots, c\}$ of positions. A sequence $B_a$ is **satisfied** if
--   1. some bin $b_j$ with $j \notin R$ receives at least one ball, or
--   2. some bin $b_j$ with $j \in R$ receives at least two balls.
--
--   Let $S$ be the number of satisfied sequences. If $c^2 < n$ and $\varepsilon > 0$, then with probability at least $1 - 2e^{-\varepsilon^2 n/2}$,
--   $$S \;\ge\; \ell\Big(1 - \frac{2^{|R|}}{e^{c}}\Big) - \varepsilon d n - \frac{2^{|R|} c^2}{e^{c}} \cdot \frac{\ell}{n - c^2}.$$
--
--   In the analysis of the two suggested matchings algorithm this bound, with $c = 2$ and $d = 2$, counts the advertisers of $A_{BR}$, $A_{BB}$ and $A_R$ that end up assigned.
--
--   **Formalization Note** Positions are $0, \dots, c-1$ (`Fin c`) rather than $1, \dots, c$. Two hypotheses that the proof (Appendix A, pp. 12–13) uses without stating are made explicit: the $c$ bins of each sequence are distinct, and $c^2 < n$, so that $n - c^2 > 0$. With a repeated bin the bound fails (for $c = 2$, $R = \emptyset$ and $B_a = (b, b)$ the sequence is unsatisfied with probability about $1/e > 1/e^2$).
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 4, Fact 2 (Section 2.1); restated p. 12 and proved p. 13, Appendix A

import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Model

namespace OnlineStochMatching.TSM

open Finset

/-- **Fact 2** (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating
1-1/e*, arXiv:0905.4100v1, §2.1, p. 4; proof App. A, pp. 12–13). Throw `n` balls i.i.d. uniformly
into `n` bins (`balls t` is the bin of ball `t`). Let `B 0, …, B (ℓ-1)` be sequences of `c`
distinct bins each (`B a j` is the `j`-th bin of the `a`-th sequence, positions `0, …, c-1`), with
no bin in more than `d` sequences, and fix a set `R` of positions. Sequence `a` is *satisfied* if
some bin at a position outside `R` has at least one ball, or some bin at a position in `R` has at
least two balls; `S` is the number of satisfied sequences. If `c² < n` and `ε > 0`, then with
probability at least `1 - 2 exp(-ε² n / 2)`,
`S ≥ ℓ (1 - 2^{|R|}/e^c) - ε d n - (2^{|R|} c² / e^c) · ℓ / (n - c²)`.

The hypotheses `c² < n` (so that `n - c² > 0`) and that the bins of each sequence are distinct are
used by the proof (the factor `(1 - c/n)^{n - |R'|}`) without being stated on the page; with
repeated bins the bound fails. -/
theorem fact_2 (n c ℓ d : ℕ) (hcn : c ^ 2 < n) (B : Fin ℓ → Fin c → Fin n)
    (hB : ∀ a, Function.Injective (B a))
    (hd : ∀ b : Fin n, (Finset.univ.filter fun a : Fin ℓ => ∃ j, B a j = b).card ≤ d)
    (R : Finset (Fin c)) (ε : ℝ) (hε : 0 < ε) :
    1 - 2 * Real.exp (-(ε ^ 2 * n / 2)) ≤
      prob n (fun balls : Fin n → Fin n =>
        (ℓ : ℝ) * (1 - 2 ^ R.card / Real.exp 1 ^ c) - ε * d * n
            - (2 ^ R.card * (c : ℝ) ^ 2 / Real.exp 1 ^ c) * ((ℓ : ℝ) / ((n : ℝ) - (c : ℝ) ^ 2)) ≤
          ((Finset.univ.filter fun a : Fin ℓ =>
              (∃ j, j ∉ R ∧ 1 ≤ (Finset.univ.filter fun t => balls t = B a j).card) ∨
              (∃ j, j ∈ R ∧ 2 ≤ (Finset.univ.filter fun t => balls t = B a j).card)).card : ℝ)) := by sorry

end OnlineStochMatching.TSM
