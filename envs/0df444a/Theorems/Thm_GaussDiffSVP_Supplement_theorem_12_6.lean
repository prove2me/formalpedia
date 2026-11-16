-- Prove2me | Theorems.Thm_GaussDiffSVP_Supplement_theorem_12_6
-- name    : GaussDiffSVP.Supplement.theorem_12_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:53:12.503461+00:00
-- url     : https://prove2.me/theorems/85dbb3a0-4f94-4bb8-bc90-a7e0397b1665
-- title:
--   Theorem 12.6 — centered DGS from an adversarial SVP oracle, $(1+1/f,2^{-f})$-close, polynomial work
-- statement:
--   Let $L=B\mathbb Z^n$ be a full rank rational lattice, $\sigma^2>0$ rational and $f\ge1$ an integer. There is an oracle algorithm whose output law $\mu$ is $(1+1/f,2^{-f})$-close to $D_{L,\sigma}$: some law $\tilde\mu$ satisfies
--   $$d_{TV}(\mu,\tilde\mu)\le2^{-f},\qquad (1+1/f)^{-1}D_{L,\sigma}(x)\le\tilde\mu(x)\le(1+1/f)D_{L,\sigma}(x)\ \text{ for every }x.$$
--   Its work, counting each SVP call as one operation, is bounded by a polynomial in $\mathrm{size}(B,\sigma^2)$ and $f$ on every execution, and so are its workspace and its number of oracle calls. Every query is a full rank sublattice of $L$ with polynomial encoding length. The guarantee holds for every oracle that returns a shortest vector of each query, choosing among shortest vectors by any rule that depends on the current and previous queries.
--
--   Replacing each oracle call by the SVP algorithm of Theorem 1.3 gives centered Gaussian samples at every width at the same exponents (Corollary 1.4).
--
--   **Formalization Note** One program and one exponent $K$ serve all inputs and all valid oracle rules; the bounds are $(\mathrm{size}(B,\sigma^2)+f+1)^K$. Laws are on output words; $D_{L,\sigma}$ on words is the published iidLaw with one sample.
--
--   Differences from the source:
--   - encoding: randomized word RAM, time in word operations, space in bits → the published randomized log-cost rational RAM TwMSOCount.Main, bit time and bit space; reason: App. C.1.1 (p.80): the same leading exponents hold with bit costs; the convention of the published goal
--   - encoding: oracle algorithm in the declared model, work counting each SVP call as one operation → oracleOutcome: segments of the published RAM, a halt with output word 1 :: q is a query, the reply is written to the output cells and the run resumes with fresh coins; work = bit time + 1 per call, workspace = maximal bit space; reason: the published RAM has no oracle instruction
--   - reading: "The oracle may choose among shortest vectors using any rule that depends on the current and previous queries" → the conclusion holds for every rule O(previous queries, current query) whose reply to every nonsingular basis word is a shortest nonzero vector of that lattice; reason: universal quantification over the adversary
--   - encoding: polynomial in size(B, σ²) and f → (size(B, σ²) + f + 1)^K with one K, size the bit length of the words of B and σ²; reason: a single polynomial bound fixed before the input
--   - encoding: output law and D_{L,σ} → laws on output words: the output is an integer coefficient vector on every coin tape, D_{L,σ} is CosetTreeSVP.SVP.iidLaw B σ 1, μ̃ a probability law on words; reason: the coefficient encoding is injective, so the laws correspond
--   - encoding: a full rank sublattice of L with polynomial encoding length → the word of a nonsingular B' ∈ ℚ^{n×n} with L(B') ⊆ L(B) and bit length ≤ (size + f + 1)^K; reason: same objects
--   - encoding: a full rank rational lattice L = Bℤⁿ → a nonsingular B ∈ ℚ^{n×n}, n ≥ 1; reason: same instances; the rank-0 lattice is excluded as in the published goal
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 12.6, p.61 (§12.1 accuracy convention, p.58; Algorithm 7 and App. D)

import Mathlib
import Definitions.Def_GaussDiffSVP_Supplement_OracleRAM

open MeasureTheory TwMSOCount.Main CosetTreeSVP.SVP
open scoped ENNReal

namespace GaussDiffSVP.Supplement

/-- Theorem 12.6 (Centered sampling from SVP) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.61). Let `L = Bℤⁿ` be a full rank rational
lattice, `σ² > 0` rational, and `f ≥ 1` an integer. There is an oracle algorithm whose output law is
`(1 + 1/f, 2^{−f})`-close to `D_{L,σ}` in the convention of Section 12.1 (p.58: a law `µ` is
`(γ, ε)`-close to `D` if some law `µ̃` satisfies `d_TV(µ, µ̃) ≤ ε` and `γ^{−1}D(x) ≤ µ̃(x) ≤ γD(x)` for
every `x`). In the declared computational model, its work, counting each SVP call as one
operation, is bounded by a polynomial in `size(B, σ²)` and `f` on every execution. The same is true
of its workspace and number of oracle calls. Every query is a full rank sublattice of `L` with
polynomial encoding length. The oracle may choose among shortest vectors using any rule that depends
on the current and previous queries.

**Formalization Note.** One oracle program `P` and one exponent `K` for all inputs and **every**
valid SVP oracle rule `O` (`IsSVPOracle`); the oracle semantics is `oracleOutcome` (an oracle
extension of the published RAM). The input word is the basis, `σ²` and `f`; `N = size(B, σ²) + f + 1`
and "polynomial" is `N^K`. Every query is the word of a nonsingular `B' ∈ ℚ^{n×n}` with
`L(B') ⊆ L(B)`. The output is an integer coefficient vector; laws are on output words, and `D_{L,σ}` on
words is the published `CosetTreeSVP.SVP.iidLaw B σ 1` (`ρ_σ(Bx)/ρ_σ(L)` at the word of `x`),
`σ = √σ²`; `d_TV` is the published `tvDist` (`½ Σ`). The law `µ̃` is a probability law on words. -/
theorem theorem_12_6 :
    ∃ (P : Program) (K : ℕ), ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
      ∀ σ2 : ℚ, 0 < σ2 → ∀ f : ℕ, 1 ≤ f →
      ∀ O : List (List ℚ) → List ℚ → List ℚ, IsSVPOracle O →
        (∀ τ : ℕ → Bool, ∃ res : OracleResult,
          oracleOutcome P O τ (SuperlatSVP.encBasis B ++ [σ2, (f : ℚ)]) = some res ∧
          (res.time : ℝ) ≤ ((wordBits (SuperlatSVP.encBasis B ++ [σ2]) : ℝ) + f + 1) ^ K ∧
          (res.space : ℝ) ≤ ((wordBits (SuperlatSVP.encBasis B ++ [σ2]) : ℝ) + f + 1) ^ K ∧
          (res.calls : ℝ) ≤ ((wordBits (SuperlatSVP.encBasis B ++ [σ2]) : ℝ) + f + 1) ^ K ∧
          (∃ x : Fin n → ℤ, res.output = SuperlatSVP.encIntVec x) ∧
          ∀ q ∈ res.queries, ∃ B' : Matrix (Fin n) (Fin n) ℚ, B'.det ≠ 0 ∧
            q = SuperlatSVP.encBasis B' ∧ latQ B' ≤ latQ B ∧
            (wordBits q : ℝ) ≤ ((wordBits (SuperlatSVP.encBasis B ++ [σ2]) : ℝ) + f + 1) ^ K) ∧
        (∀ o : List ℚ, MeasurableSet {τ | (oracleOutcome P O τ
          (SuperlatSVP.encBasis B ++ [σ2, (f : ℚ)])).map OracleResult.output = some o}) ∧
        ∃ μt : List ℚ → ℝ≥0∞, ∑' o, μt o = 1 ∧
          tvDist (fun o => coinTape {τ | (oracleOutcome P O τ
              (SuperlatSVP.encBasis B ++ [σ2, (f : ℚ)])).map OracleResult.output = some o}) μt ≤
            ENNReal.ofReal ((2 : ℝ) ^ (-(f : ℝ))) ∧
          ∀ o : List ℚ,
            (ENNReal.ofReal (1 + 1 / (f : ℝ)))⁻¹ * iidLaw B (Real.sqrt (σ2 : ℝ)) 1 o ≤ μt o ∧
            μt o ≤ ENNReal.ofReal (1 + 1 / (f : ℝ)) * iidLaw B (Real.sqrt (σ2 : ℝ)) 1 o := by sorry

end GaussDiffSVP.Supplement
