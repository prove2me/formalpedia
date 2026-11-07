-- Prove2me | Theorems.Thm_LIPAlgorithm_theorem_7_1
-- name    : LIPAlgorithm.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:29.831358+00:00
-- url     : https://prove2.me/theorems/9588eb9f-eff7-4a13-ae85-2fab3390c569
-- title:
--   Theorem 7.1 — well-rounded all-isomorphism algorithm
-- statement:
--   There are a machine and constants $C,K,\kappa_0$, $c>0$ with the following property. For $n\ge1$, integral well-rounded positive definite $G_1,G_2\in\mathbb Z^{n\times n}$ of encoding length $\ell$ and $\kappa\ge\kappa_0n\log n$, set $T=\lceil(Cn\sqrt{\log(n+2)})^n\,2^{(\log_2(\kappa+2))^K}(\kappa+\ell+1)^K\rceil$. On input $\kappa$ (in unary), $G_1,G_2$ and $T$ coins, the machine halts within $2T$ steps on every coin string, and for a fraction at least
--
--   $$1-\exp(-c\kappa)$$
--
--   of the coin strings it outputs a duplicate-free list of exactly $\mathrm{Iso}(G_1,G_2)$.
--
--   This is the birthday algorithm, the node at which the recursion of the general algorithm does its main work.
--
--   Differences from the source:
--   - reading: a randomized algorithm, in an unnamed machine model → one Mathlib TM2 machine, with runs counted per input (Turing.TM2OutputsInTime); reason: the paper names no model; TM2 is the strongest standard reading, and the only steps above 2^{O(n)} (table, duplicate removal, cross-product filter) run on stacks with near-linear overhead, so the bound survives
--   - encoding: time O(n√log n)ⁿ·2^{polylog(κ)}·poly(κ) → budgetWR, with a common K and the polynomial factor (κ+ℓ+1)^K; reason: footnote 2, Remark 2.2; log(n+2) replaces log n, which is 0 at n = 1
--   - reading: randomized time → halts within 2T steps on every string of exactly T coins, which are a suffix of the input; reason: the proof caps counts, norms and lifts, so the worst case is what it provides; a TM2 has to pop unused coins before halting
--   - reading: Algorithm 1 computes Iso(L₁, L₂) → a machine outputs a duplicate-free list of exactly Iso(G₁, G₂); reason: Algorithm 1 removes duplicates (line 37); the algorithm is internal to the proof
--   - encoding: rank-n well-rounded integral lattices → Gram matrices that are integral, positive definite and well-rounded in the norm ‖z‖_G; reason: §2.2, p.10 and p.9
--   - encoding: the parameter κ of the algorithm → κ written in unary before the instance, κ ∈ ℕ, and the range κ ≥ κ₀·n·log n with the natural log and κ₀ ∈ ℕ; reason: the machine must receive κ, and the time bound is polynomial in κ, so the unary prefix costs nothing; a change of log base or rounding κ₀ up only rescales κ₀
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Theorem 7.1, p.38

import Mathlib
import Definitions.Def_LIPAlgorithm_encInst
import Definitions.Def_LIPAlgorithm_RunsWithin

namespace LIPAlgorithm

/-- **Theorem 7.1 (Well-rounded all-isomorphism algorithm).** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript
sha256 61ee52aa…), Theorem 7.1, p.38 (PDF p.41).

One machine and constants `C`, `K`, `c > 0`, `κ₀`, before the instance: for `n ≥ 1`, integral well-rounded `G₁`, `G₂` and
`κ ≥ κ₀·n·log n`, with `T = ⌈(C·n·√log(n+2))ⁿ·2^{(log₂(κ+2))^K}·(κ+ℓ+1)^K⌉`, the machine reads `κ` in unary, then the
instance, then `T` coins. It halts within `2T` steps on all coins, and for a fraction at least `1 − exp(−c·κ)` of them it
outputs a duplicate-free list of exactly `Iso(G₁, G₂)`.

**Formalization Note.** The machine conventions are those of `theorem_1_1`. The paper's "Algorithm 1" is existential here. -/
theorem theorem_7_1 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C K κ₀ : ℕ) (c : ℝ), 0 < c ∧
      ∀ (n : ℕ) (G₁ G₂ : Gram n) (κ : ℕ), 1 ≤ n → IsGram G₁ → IsGram G₂ →
        IsWellRoundedGram G₁ → IsWellRoundedGram G₂ →
        (κ₀ : ℝ) * n * Real.log n ≤ κ →
        let inp := List.replicate κ true ++ [false] ++ encInst G₁ G₂
        let T := budgetWR C K n κ (encInst G₁ G₂).length
        (∀ coins : List.Vector Bool T, ∃ out, RunsWithin M (inp ++ coins.toList) out (2 * T)) ∧
        1 - Real.exp (-(c * κ)) ≤
          coinFraction T fun coins =>
            ∃ Us : List (Gram n), Us.Nodup ∧ (∀ U, U ∈ Us ↔ U ∈ isoSet G₁ G₂) ∧
              RunsWithin M (inp ++ coins) (encMatList Us) (2 * T) := by sorry

end LIPAlgorithm
