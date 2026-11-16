-- Prove2me | Theorems.Thm_GaussDiffSVP_Supplement_theorem_12_3
-- name    : GaussDiffSVP.Supplement.theorem_12_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:51:47.254365+00:00
-- url     : https://prove2.me/theorems/f26d4558-5da8-42b8-b9cf-7217fd781965
-- title:
--   Theorem 12.3 — exact $g$-uSVP from an $r$-BDD interface in time $\mathrm{poly}\cdot[P+\max\{1,(gr)^{-n}\}D]$
-- statement:
--   Assume an $r$-BDD interface with $0<r<1/2$, preprocessing $P$, query work $D$ and space $S$, whose advice determines, with probability at least $9/10$, a function correct on all promised rational targets, and whose query function has a fixed resource bound even outside the promise. For every fixed $g\ge1$, exact $g$-uSVP, with promise
--   $$\lambda_2(L)\ge g\,\lambda_1(L),$$
--   is solvable with probability at least $2/3$ in time and space
--   $$T\le\mathrm{poly}(n,B)\big[P+\max\{1,(gr)^{-n}\}D\big],\qquad S+\mathrm{poly}(n,B).\tag{130}$$
--   At $g=1$ the problem is ordinary SVP.
--
--   Reusable decoding thus solves unique SVP with a single preprocessing per sublattice and an explicit exponential number of queries below the radius $1/g$.
--
--   **Formalization Note** The input is the basis word; success is a shortest nonzero vector, output as integer coefficients. $\lambda_2$ is $\infty$ in rank one, where the promise holds.
--
--   Differences from the source:
--   - encoding: randomized word RAM, time in word operations, space in bits → the published randomized log-cost rational RAM TwMSOCount.Main, bit time and bit space; reason: App. C.1.1 (p.80): the same leading exponents hold with bit costs; the convention of the published goal
--   - reading: "Assume an r-BDD interface with 0 < r < 1/2 … With probability at least 9/10 …" (§12.3, p.59) → hypothesis IsBDDInterface r Pre Q P D S K (9/10) with 0 < r < 1/2, for every n ≥ 1 and every nonsingular rational basis; reason: the standing assumption of §12.3, stated once for the section
--   - encoding: poly(n, B) and "S + poly(n, B)" → (ℓ+1)^{K'} with K' and the program fixed after the fixed parameters and the interface, before the input; space (S(n)+1)(ℓ+1)^{K'}; reason: S already suppresses polynomial factors (it is S(n) times (ℓ+1)^K in the interface)
--   - reading: time and space bounds of the reduction → on every coin tape for every nonsingular input, also outside the promise; reason: "All resource bounds hold on every execution" (p.6, p.80); the stronger reading
--   - encoding: λ₂(L) → lam2 with values in ℝ≥0∞ (∞ in rank one); reason: an infimum over an empty set is +∞, as the paper's "Rank one is immediate" presumes
--   - encoding: exact g-uSVP solution → the integer coefficient vector of a shortest nonzero vector (SuperlatSVP.svpSuccess), probability ≥ 2/3 on promise inputs; reason: convention of the published goal
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 12.3, p.59 ((130), p.59; §12.3 interface, p.59; proof App. F.2, p.104)

import Mathlib
import Definitions.Def_GaussDiffSVP_Supplement_BDD

open MeasureTheory TwMSOCount.Main CosetTreeSVP.SVP
open scoped ENNReal

namespace GaussDiffSVP.Supplement

/-- Theorem 12.3 (Direct unique-SVP tradeoff) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.59), under the standing assumption of §12.3
(p.59): "Assume an r-BDD interface with `0 < r < 1/2`, preprocessing `P`, query work `D`, and
space `S`. With probability at least 9/10 its advice determines a function correct on all promised
rational targets. The function has a fixed resource bound even outside the promise."

For every fixed `g ≥ 1`, exact `g`-uSVP, with promise `λ₂(L) ≥ gλ₁(L)`, is solvable with
probability at least `2/3` in time and space
`T ≤ poly(n, B)[P + max{1, (gr)^{−n}} D]`, `S + poly(n, B)` (130). At `g = 1` the problem is
ordinary SVP.

**Formalization Note.** The interface is `IsBDDInterface r Pre Q P D S K (9/10)` (every `n ≥ 1`,
every nonsingular rational basis). The uSVP program `P'` and the exponent `K'` may depend on `g`,
`r`, the interface's programs and `K`, and are fixed before `n` and `B`; `poly(n, B)` is
`(ℓ+1)^{K'}`, `ℓ` the bit length of `B`, so the space bound `S + poly` reads
`(S(n) + 1)(ℓ+1)^{K'}`. The resource bounds hold on every coin tape for every nonsingular input;
success (a shortest nonzero vector as integer coefficients, `SuperlatSVP.svpSuccess`) is required on
promise inputs. `λ₂` is `lam2` (`∞` in rank one). -/
theorem theorem_12_3 (r : ℝ) (hr0 : 0 < r) (hr : r < 1 / 2) (Pre Q : Program)
    (P D S : ℕ → ℝ) (K : ℕ) (hI : IsBDDInterface r Pre Q P D S K (fun _ => 9 / 10))
    (g : ℝ) (hg : 1 ≤ g) :
    ∃ (P' : Program) (K' : ℕ), ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
      (∀ τ : ℕ → Bool, ∃ s : RunStats,
        runStats P' τ (Config.init (SuperlatSVP.encBasis B)) = some s ∧
        (s.time : ℝ) ≤ ((SuperlatSVP.inputBits B : ℝ) + 1) ^ K' *
          (P n + max 1 ((g * r) ^ (-(n : ℝ))) * D n) ∧
        (s.space : ℝ) ≤ (S n + 1) * ((SuperlatSVP.inputBits B : ℝ) + 1) ^ K') ∧
      (ENNReal.ofReal (g * SuperlatSVP.lam1 (latQ B)) ≤ lam2 (latQ B) →
        MeasurableSet (SuperlatSVP.svpSuccess P' B) ∧
          (2 / 3 : ℝ≥0∞) ≤ coinTape (SuperlatSVP.svpSuccess P' B)) := by sorry

end GaussDiffSVP.Supplement
