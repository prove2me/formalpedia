-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_theorem_3_3
-- name    : LatticeAvgPrec.OneVector.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:51:34.329405+00:00
-- url     : https://prove2.me/theorems/8456297c-9185-4df0-8959-b6f68355727a
-- title:
--   Theorem 3.3 — Black-box conversion
-- statement:
--   Let $c_0>0$ be the approximation exponent of a single-vector oracle (Definition 3.2). There are constants $C_1,C_2,c>0$, depending only on $c_0$, such that for every available exponent $\omega$, $2<\omega\le3$, there are programs $\mathrm{Pre}$, $\mathrm{Post}$, a subpolynomial factor $g$ and, for each input, bounds $k$ and $h$, such that for every $H\in\mathbb Z^{n\times n}$ in HNF ($n\ge1$) with $\mathcal D=\log_2\det H$:
--
--   1. $k\le C_1n$, $k\le h\le C_2(\mathcal D/k+k)$;
--   2. $\mathrm{Pre}$ on $H$ is Las Vegas within expected cost $\widetilde O(n^{\omega-1}(\mathcal D+n))$ and either returns $v$ directly, or makes the single oracle call: it outputs a nonsingular integer $E$ of dimension $k'\le k$ with $\|E\|_2\le2^h$, $\|E^{-1}\|_2\le2$ and auxiliary data;
--   3. for **every** valid oracle answer $0\ne w\in E\mathbb Z^{k'}$, $\|w\|_2\le2^{c_0k'}\lambda_1(E\mathbb Z^{k'})$, $\mathrm{Post}$ on (auxiliary data, $w$) is Las Vegas within expected cost $\widetilde O(n^{\omega-1}(\mathcal D+n))$;
--   4. every oracle with cost bound $\mathsf T$ answers that call within expected cost $\mathsf T(k,h)$;
--
--   and the returned vector satisfies
--   $$0\ne v\in\Lambda(H),\qquad \|v\|_2\le 2^{cn}\lambda_1(\Lambda(H)),\qquad \|v\|_2\le 2^{cn}2^{\mathcal D/n}.$$
--   The total expected bit cost is therefore $\mathsf T(k,h)+\widetilde O(n^{\omega-1}(\mathcal D+n))$, input and output included.
--
--   This conversion is how one approximate-SVP call on an $O(n)$-dimensional, well-conditioned matrix of height $O(\mathcal D/k+k)$ yields a short vector of an arbitrary HNF lattice.
--
--   **Formalization Note** The printed theorem's "at most one oracle call" is rendered by the Pre/Post decomposition (tag cell $0$: direct answer; tag cell $1$: query $E$ followed by the auxiliary list). The bounds $k,h$ are functions of the input chosen with the programs.
--
--   Differences from the source:
--   - reading: costs measured in bit operations, with quasi-linear scalar integer arithmetic; Las Vegas expected cost → bit cost of a program of the published logarithmic-cost RAM (TimeSpaceMA_RAM with the cost layer SoftmaxAttnFD_Machine): each instruction costs 1 plus the bit sizes of every address and value it touches; LasVegasWithin: correct on every halting coin tape, expected cost at most the bound; reason: the paper names no machine; the matrix-multiplication hypothesis MatMulAvailable is stated in the same model, so the reading neither adds nor removes power
--   - reading: Õ(f) suppresses subpolynomial factors in the dimension and precision parameters (p.4) → g(n, ⌈𝒟⌉)·f with g subpolynomial (IsSubpoly: for every ε > 0, g x y ≤ C_ε (x + y + 2)^ε), g chosen with the program before every input; reason: the p.4 convention made uniform; a factor fixed before the input is the honest reading of Õ
--   - encoding: binary input and output → integers coded one bit per memory cell (natCode / intCode, self-delimiting), vectors and matrices with their dimensions first, input from cell 0 (memOf), output held from cell 0 (memHolds); reason: keeps the bit count of the binary representation; the codes are prefix-free, so the output is read unambiguously
--   - encoding: n×n matrices with an implicit positive dimension → 1 ≤ n; reason: at n = 0 the cost bound is 0 while every run costs at least 1; the 0-dimensional case is degenerate and not considered by the source
--   - encoding: a fixed available matrix-multiplication exponent 2 < ω ≤ 3; multiplying order-n integer matrices with b-bit entries costs Õ(n^ω b) (pp.4, 9) → hypotheses 2 < ω ≤ 3 and MatMulAvailable ω (a coin-free RAM program multiplies such matrices within g₀(n,b)·n^ω·b, g₀ subpolynomial); reason: the paper's standing assumption stated as a hypothesis; ω = 3 satisfies it, so the statement is not vacuous
--   - generalization: the conversion calls a fixed oracle R satisfying Definition 3.2 and post-processes its answer → Post returns a correct v for every w with 0 ≠ w ∈ Eℤ^k, ‖w‖₂ ≤ 2^{c₀k} λ₁(Eℤ^k), whichever oracle produced it; reason: every answer of an oracle meeting Definition 3.2 is such a w, so the printed conversion is the special case
--   - reading: the total expected bit cost is T(k,h) + Õ(n^{ω−1}(𝒟+n)) → Pre's and Post's expected costs are each at most g·n^{ω−1}(𝒟+n), and every oracle meeting Definition 3.2 answers the single query within expected cost T(k,h), with k, h functions of the input; reason: a black-box oracle call is charged T(k,h); on the RAM a subroutine call has no separate cost, so the total is stated as the sum of the three parts
--   - reading: coordinate projection, exact power-of-two rescaling and zero padding return v → no separate clause; Post's correctness and cost bound; reason: the sentence describes how v is obtained; its quantitative content is Post's cost bound
--   - encoding: 2^{O(k)} in Definition 3.2 and 2^{O(n)} in the conclusion, hidden constants depending only on the oracle's guarantee; h real → ∀ c₀ > 0, then ∃ C₁, C₂, c > 0, then ∀ ω, then ∃ programs and g; h and T on natural numbers; reason: the hidden constants come after c₀ and before ω and every input, so they depend only on the oracle's guarantee; an oracle bound on all real h restricts to natural h
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Theorem 3.3, p. 12

import Definitions.Def_LatticeAvgPrec_OneVector_Cost
open Matrix

namespace LatticeAvgPrec.OneVector

/-- **Theorem 3.3** (Black-box conversion; STOC 2027 submission #1574, p.12). Fix a single-vector
oracle `R` (Definition 3.2) with nondecreasing cost bound `T`. For `H ∈ ℤ^{n×n}` in HNF with
`D = log det H`, the conversion makes at most one oracle call on a nonsingular integer `E` of
dimension at most `k`, where `k = O(n)`, `k ≤ h = O(D/k + k)`, `‖E‖₂ ≤ 2^h`, `‖E⁻¹‖₂ ≤ 2`, and
returns `0 ≠ v ∈ Λ(H)` with `‖v‖₂ ≤ 2^{O(n)} λ₁(Λ(H))` and `‖v‖₂ ≤ 2^{O(n)} 2^{D/n}`, the hidden
constants depending only on the oracle's approximation guarantee; total expected bit cost
`T(k, h) + Õ(n^{ω−1}(D + n))`, input and output included.

**Formalization Note** "At most one oracle call" is a decomposition: `Pre` either answers
directly (tag `0`) or writes one oracle query `E` with auxiliary data (tag `1`); `Post` turns
**every** valid oracle answer `w` for `E` into the final vector. The total cost is the sum of
`Pre`'s expected cost, the single oracle call's expected cost (at most `T(k, h)` for every
oracle meeting Definition 3.2), and `Post`'s expected cost. The constants `C₁, C₂` (of `k = O(n)`,
`h = O(D/k + k)`) and `c` (of `2^{O(n)}`) are chosen after the oracle exponent `c₀` and before `ω`:
they depend only on the oracle's approximation guarantee, as printed. -/
theorem theorem_3_3 (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ (C₁ C₂ c : ℝ), 0 < C₁ ∧ 0 < C₂ ∧ 0 < c ∧
    ∀ (ω : ℝ), 2 < ω → ω ≤ 3 → MatMulAvailable ω →
    ∃ (Pre Post : TimeSpaceMA.Program) (g : ℕ → ℕ → ℝ)
      (kb hb : (n : ℕ) → Matrix (Fin n) (Fin n) ℤ → ℕ), IsSubpoly g ∧
      ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ), 1 ≤ n → IsHNF H →
        ((kb n H : ℝ) ≤ C₁ * n ∧ kb n H ≤ hb n H ∧
          (hb n H : ℝ) ≤ C₂ * (Real.logb 2 (H.det : ℝ) / kb n H + kb n H)) ∧
        SoftmaxAttnFD.LasVegasWithin Pre (TimeSpaceMA.memOf (matCode H))
          (fun mem =>
            (∃ v : Fin n → ℤ, memHolds mem (0 :: vecCode v) ∧ HNFVecGood c H v) ∨
            (∃ (k : ℕ) (E : Matrix (Fin k) (Fin k) ℤ) (aux : List ℕ),
              memHolds mem (1 :: (matCode E ++ listCode aux)) ∧
              1 ≤ k ∧ k ≤ kb n H ∧ E.det ≠ 0 ∧
              specNorm (rmat E) ≤ (2 : ℝ) ^ (hb n H) ∧ specNorm (rmat E)⁻¹ ≤ 2 ∧
              (∀ w : Fin k → ℤ, w ≠ 0 → w ∈ lat E →
                ivNorm w ≤ (2 : ℝ) ^ (c₀ * k) * lam (lat E) 1 →
                SoftmaxAttnFD.LasVegasWithin Post
                  (TimeSpaceMA.memOf (listCode aux ++ vecCode w))
                  (fun mem' => ∃ v : Fin n → ℤ, memHolds mem' (vecCode v) ∧ HNFVecGood c H v)
                  (g n ⌈Real.logb 2 (H.det : ℝ)⌉₊ * (n : ℝ) ^ (ω - 1) *
                    (Real.logb 2 (H.det : ℝ) + n))) ∧
              (∀ (R : TimeSpaceMA.Program) (T : ℕ → ℕ → ℝ), IsSingleVectorOracle c₀ R T →
                SoftmaxAttnFD.LasVegasWithin R (TimeSpaceMA.memOf (matCode E))
                  (OracleOut c₀ E) (T (kb n H) (hb n H)))))
          (g n ⌈Real.logb 2 (H.det : ℝ)⌉₊ * (n : ℝ) ^ (ω - 1) *
            (Real.logb 2 (H.det : ℝ) + n)) := by sorry

end LatticeAvgPrec.OneVector
