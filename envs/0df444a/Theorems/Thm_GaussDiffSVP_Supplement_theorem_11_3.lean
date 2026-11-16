-- Prove2me | Theorems.Thm_GaussDiffSVP_Supplement_theorem_11_3
-- name    : GaussDiffSVP.Supplement.theorem_11_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:50:43.623037+00:00
-- url     : https://prove2.me/theorems/0f0e4dc8-e9a0-4cf0-a471-7c0dc51638d6
-- title:
--   Theorem 11.3 — full batches of $\lfloor 2^{\beta_G n}\rfloor$ samples at width $3\eta_{1/2}/2$
-- statement:
--   Write $\alpha_G=\tfrac12\log_2(3/2)$ and $\beta_G=\tfrac12\log_2(4/3)$. Given a full rank rational lattice $L=B\mathbb Z^n$, a rational shift $a$ and a positive rational squared width $\sigma^2$ with
--   $$\sigma\ge\tfrac32\,\eta_{1/2}(L),$$
--   the algorithm outputs $\lfloor2^{\beta_G n}\rfloor$ points of $a+L$ jointly within $\exp[-\Omega(n/\log^2(n+2))]$ in total variation of $D_{a+L,\sigma}^{\otimes\lfloor2^{\beta_G n}\rfloor}$, in time $2^{\alpha_G n+o(n)}$ and bit space $2^{\beta_G n+o(n)}$.
--
--   This is the full-size strengthening of Theorem 11.2 at width $3/2$; it supplies the dual samples behind the best BDD radius of Theorem 12.1.
--
--   **Formalization Note** One program, $g$, $K$ and $c>0$ for all inputs; the batch size is $\lfloor2^{\beta_G n}\rfloor$.
--
--   Differences from the source:
--   - encoding: randomized word RAM, time in word operations, space in bits → the published randomized log-cost rational RAM TwMSOCount.Main, bit time and bit space; reason: App. C.1.1 (p.80): the same leading exponents hold with bit costs; the convention of the published goal
--   - encoding: o(n), exp[−Ω(·)], suppressed polynomial factors in the input length → one g with g(n)/n → 0, exp(−c·(·)) with one c > 0 for every n ≥ 1, a factor (ℓ+1)^K; program, g, K, c fixed after the fixed parameters and before n and the input; reason: reading of the asymptotic notation as in the published goal; App. C.1.4 (p.81) covers the finitely many small ranks
--   - encoding: output points X ∈ a + L and their law → rational coordinate words, every output on every coin tape a tuple of points of a + L, total variation ½Σ over output words; reason: points of a + L are rational and the word encoding is injective, so the laws correspond
--   - encoding: η_ε(L) defined by ρ_{1/η}(L*∖{0}) = ε → the published smoothingParam, the infimum of s > 0 with ρ_{1/s}(L*∖{0}) ≤ ε; reason: the dual mass is continuous and strictly decreasing in s, so both give the same value
--   - encoding: a full rank rational lattice L = Bℤⁿ → a nonsingular B ∈ ℚ^{n×n}, n ≥ 1; reason: same instances; the rank-0 lattice is excluded as in the published goal
--   - reading: "the algorithm" (Algorithm 6 in full batch mode), on the inputs of Theorem 1.2 → there exists a program; the inputs are a nonsingular B ∈ ℚ^{n×n}, a ∈ ℚⁿ and a rational σ² > 0 with 3η_{1/2}(L)/2 ≤ σ; reason: the theorem asserts the guarantee of a specific algorithm; its formal content is that some program achieves it
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 11.3, p.56 (Algorithm 6, p.57; inputs of Theorem 1.2, p.6)

import Mathlib
import Definitions.Def_GaussDiffSVP_Supplement_DGS

open Filter Topology TwMSOCount.Main CosetTreeSVP.SVP

namespace GaussDiffSVP.Supplement

/-- Theorem 11.3 (Full batches at width 3/2) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.56). If `σ ≥ 3η_{1/2}(L)/2`, the algorithm
outputs `⌊2^{β_G n}⌋` points jointly within `exp[−Ω(n / log²(n + 2))]` of
`D_{a+L,σ}^{⊗⌊2^{β_G n}⌋}`, in time `2^{α_G n + o(n)}` and bit space `2^{β_G n + o(n)}`.

The inputs are those of Theorem 1.2 (p.6): a full rank rational lattice `L = Bℤⁿ`, a rational shift
`a` and a positive rational squared width `σ²`.

**Formalization Note.** `α_G = ½ log₂(3/2)`, `β_G = ½ log₂(4/3)`; one program `P`, one `g` with
`g(n)/n → 0`, one `K` and one `c > 0`, fixed before `n` and the input; `Ω(·)` is `c·(·)` for every
`n ≥ 1`; `log` natural; the batch size is `Nat.floor (2^{β_G n})`. -/
theorem theorem_11_3 :
    ∃ (P : Program) (g : ℕ → ℝ) (K : ℕ) (c : ℝ),
      Tendsto (fun n : ℕ => g n / n) atTop (𝓝 0) ∧ 0 < c ∧
      ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
      ∀ (a : Fin n → ℚ) (σ2 : ℚ), 0 < σ2 →
        3 * RegevLWE.GaussConv.smoothingParam (latQ B) (1 / 2) / 2 ≤ Real.sqrt (σ2 : ℝ) →
        SamplesDGSWithin P K ((2 : ℝ) ^ (1 / 2 * Real.logb 2 (3 / 2) * n + g n))
          ((2 : ℝ) ^ (1 / 2 * Real.logb 2 (4 / 3) * n + g n))
          (Real.exp (-(c * n / Real.log ((n : ℝ) + 2) ^ 2)))
          ⌊(2 : ℝ) ^ (1 / 2 * Real.logb 2 (4 / 3) * n)⌋₊ B a σ2 := by sorry

end GaussDiffSVP.Supplement
