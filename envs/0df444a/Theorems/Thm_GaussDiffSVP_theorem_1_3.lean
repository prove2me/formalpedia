-- Prove2me | Theorems.Thm_GaussDiffSVP_theorem_1_3
-- name    : GaussDiffSVP.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:59:45.664378+00:00
-- url     : https://prove2.me/theorems/703e0943-5498-4a66-95bc-6c0dd3e6635d
-- title:
--   Theorem 1.3 — exact SVP in time $2^{0.4130n+o(n)}$ and space $2^{0.3138n+o(n)}$ with probability $1-2^{-\Omega(n\log n)}$
-- statement:
--   Given a full-rank rational lattice $L = B\mathbb Z^n$, there is a classical randomized algorithm that returns a shortest nonzero vector with probability at least $1-2^{-\Omega(n\log n)}$, in time
--   $$T = 2^{0.4130n+o(n)},\qquad S = 2^{0.3138n+o(n)}$$
--   space. Every output is a nonzero vector of $L$.
--
--   Precisely: there are one program $P$ of the randomized log-cost rational RAM, one function $g$ with $g(n)/n\to0$, one exponent $K$ and one constant $c>0$ such that for every $n\ge1$ and every nonsingular $B\in\mathbb Q^{n\times n}$, on every coin tape $P$ halts within bit time $2^{0.4130n+g(n)}(\ell+1)^K$ and bit space $2^{0.3138n+g(n)}(\ell+1)^K$ ($\ell$ the input length) and outputs the coefficients of a nonzero lattice vector, and with probability at least $1-2^{-cn\log_2n}$ the output is a shortest nonzero vector. This is the first provable exact SVP algorithm below the $2^{n/2}$ time barrier.
--
--   Differences from the source:
--   - reading: randomized word RAM, $w = \Theta(n+\log(\mathcal B+2))$, time in word operations, space in bits → the published randomized log-cost rational RAM `TwMSOCount.Main`, bit time and bit space; reason: App. C.1.1: the same leading exponents hold with bit costs; a word operation costs $\mathrm{poly}(n,\log\mathcal B)$ bit operations, absorbed by $2^{g(n)}(\ell+1)^K$
--   - reading: polynomial factors in the input length suppressed (p.6) → a factor $(\ell+1)^K$ with $K$ fixed before $n$ and $B$; reason: the paper's convention
--   - encoding: $o(n)$ in $T$ and $S$ → one $g$ with $g(n)/n\to0$, the same for time and space, fixed before $n$ and $B$; reason: constants are uniform (p.17)
--   - reading: $1-2^{-\Omega(n\log n)}$ → $1-2^{-cn\log_2n}$ with one $c>0$ for every $n\ge1$; reason: fixed dimensions are handled by exact SVP (App. C.1.4); vacuous at $n=1$
--   - encoding: a full-rank rational lattice $L = B\mathbb Z^n$; the output → $B\in\mathbb Q^{n\times n}$ with $\det B\ne0$ read through `SuperlatSVP.encBasis`; the output is the integer coefficient vector; reason: the coefficient vector determines the lattice vector
--   - encoding: every output is a nonzero vector of $L$ → the every-tape output clause of `SolvesSVPWithProb`; reason: on every execution
--   - reading: returns a shortest nonzero vector → `SuperlatSVP.IsShortest`: $Bx\ne0$ and $\|Bx\|^2\le\|By\|^2$ for all $y\ne0$; reason: $\|Bx\| = \lambda_1(L)$
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 1.3, p.7; §1.2, p.6; App. C.1.1, p.80

import Mathlib
import Definitions.Def_GaussDiffSVP_SolvesSVPWithProb

open Filter Topology TwMSOCount.Main

namespace GaussDiffSVP

/-- Theorem 1.3 (SVP) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.7). Given a full-rank rational lattice `L = Bℤⁿ`, there is a classical
randomized algorithm that returns a shortest nonzero vector with probability at least
`1 − 2^{−Ω(n log n)}`, in time `T = 2^{0.4130n + o(n)}` and space `S = 2^{0.3138n + o(n)}`. Every
output is a nonzero vector of `L`.

Formally: one program `P` of the randomized log-cost rational RAM, one function `g` with
`g(n)/n → 0`, one exponent `K` and one constant `c > 0`, all fixed before `n` and `B`, such that for
every `n ≥ 1` and every nonsingular `B ∈ ℚ^{n×n}`: on every coin tape `P` halts within bit time
`2^{0.4130n + g(n)}(ℓ + 1)^K` and bit space `2^{0.3138n + g(n)}(ℓ + 1)^K` (`ℓ` the input length)
and outputs a nonzero lattice vector, and with probability at least `1 − 2^{−c n log₂ n}` the output
is a shortest nonzero vector.

**Formalization Note.** See `SolvesSVPWithProb` for the machine, the input word and the output
convention (integer coefficient vector). Polynomial factors in the input length are suppressed by
the paper (p.6) and appear as `(ℓ + 1)^K`. `o(n)` is one `g`, the same for time and space;
`Ω(n log n)` is `c n log₂ n` with one `c > 0` for every `n ≥ 1` (vacuous at `n = 1`). The exponents
are the exact rationals `4130/10000` and `3138/10000`. -/
theorem theorem_1_3 :
    ∃ (P : Program) (g : ℕ → ℝ) (K : ℕ) (c : ℝ),
      Tendsto (fun n : ℕ => g n / n) atTop (𝓝 0) ∧ 0 < c ∧
      ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
        SolvesSVPWithProb P K ((2 : ℝ) ^ ((4130 / 10000 : ℝ) * n + g n))
          ((2 : ℝ) ^ ((3138 / 10000 : ℝ) * n + g n))
          (1 - (2 : ℝ) ^ (-(c * n * Real.logb 2 n))) B := by sorry

end GaussDiffSVP
