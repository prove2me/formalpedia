-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_lemma_4_4
-- name    : LatticeAvgPrec.OneVector.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:51:12.295419+00:00
-- url     : https://prove2.me/theorems/8e31fe76-ac99-47af-bcbe-64c06a4a8c35
-- title:
--   Lemma 4.4 — Basis reduction with conditioning bounds
-- statement:
--   Let $\omega$ be an available exponent, $2<\omega\le3$. Let $E\in\mathbb Z^{k\times k}$ ($k\ge1$) be nonsingular with $\|E\|_2,\|E^{-1}\|_2\le2^h$ and $h\ge k$. In deterministic $\widetilde O(k^\omega h)$ time, including input and output, one can compute $U\in\mathrm{GL}_k(\mathbb Z)$, the basis $Y=EU$, and positive dyadic $\widetilde\rho_i$ such that, for the Gram–Schmidt lengths $\rho_i$ of $Y$ (the diagonal of its positive QR factor),
--   $$\widetilde\rho_i\le\rho_i\le4\widetilde\rho_i,\qquad \|Y_j\|_2\le 2^{ck}\rho_i\quad(j\le i),\qquad \kappa_{\rm col}(Y)\le 2^{ck}.$$
--   Consequently $\|Y_i\|_2\le 2^{ck}\lambda_i(E\mathbb Z^k)$ for every $i$. The matrix $U$ has $\widetilde O(h)$-bit entries.
--
--   Keeping the first column of $Y$ implements the single-vector oracle of Definition 3.2 deterministically with $\mathsf T(k,h)=\widetilde O(k^\omega h)$; this is how Corollary 3.4 instantiates Theorem 3.3.
--
--   **Formalization Note** The program receives $(h,E)$ and outputs the codes of $U$, $Y$ and $(\widetilde\rho_i)$, with $\widetilde\rho_i=\mathrm{num}_i/2^{\mathrm{ex}_i}$. Columns are indexed from $0$, so column $i$ is compared with $\lambda_{i+1}$. The constant $c$ of $2^{O(k)}$ and the factor $g(k,h)$ of both $\widetilde O$'s are chosen before the input.
--
--   Differences from the source:
--   - reading: costs measured in bit operations, with quasi-linear scalar integer arithmetic; deterministic cost → bit cost of a program of the published logarithmic-cost RAM (TimeSpaceMA_RAM with the cost layer SoftmaxAttnFD_Machine): each instruction costs 1 plus the bit sizes of every address and value it touches; DeterministicWithin: coin-free, halts within the bound on every tape with a correct output; reason: the paper names no machine; the matrix-multiplication hypothesis MatMulAvailable is stated in the same model, so the reading neither adds nor removes power
--   - reading: Õ(f) suppresses subpolynomial factors in the dimension and precision parameters (p.4) → g(k, h)·f with g subpolynomial (IsSubpoly: for every ε > 0, g x y ≤ C_ε (x + y + 2)^ε), g chosen with the program before every input; reason: the p.4 convention made uniform; a factor fixed before the input is the honest reading of Õ
--   - encoding: binary input and output → integers coded one bit per memory cell (natCode / intCode, self-delimiting), vectors and matrices with their dimensions first, input from cell 0 (memOf), output held from cell 0 (memHolds); reason: keeps the bit count of the binary representation; the codes are prefix-free, so the output is read unambiguously
--   - encoding: a fixed available matrix-multiplication exponent 2 < ω ≤ 3; multiplying order-n integer matrices with b-bit entries costs Õ(n^ω b) (pp.4, 9) → hypotheses 2 < ω ≤ 3 and MatMulAvailable ω (a coin-free RAM program multiplies such matrices within g₀(n,b)·n^ω·b, g₀ subpolynomial); reason: the paper's standing assumption stated as a hypothesis; ω = 3 satisfies it, so the statement is not vacuous
--   - encoding: k×k matrices with an implicit positive dimension → 1 ≤ k; reason: at k = 0 the cost bound is 0 while every run costs at least 1; the 0-dimensional case is degenerate and not considered by the source
--   - reading: Let E … with ‖E‖₂, ‖E⁻¹‖₂ ≤ 2^h and h ≥ k … one can compute → the program receives (h, E); reason: h is the parameter of the cost bound and of the guarantee; reading it from the input is the natural reading of the statement
--   - encoding: Gram–Schmidt lengths ρ_i of Y; indices 1 ≤ i ≤ k → ρ_i = R_ii for every positive QR factorization Y = OR (unique); Fin k indices, λ_{i+1} for column i; reason: the paper defines Gram–Schmidt lengths as the diagonal of the positive QR factor (App. A); 0-based indexing changes no instance
--   - encoding: 2^{O(k)} → 2^(c·k) with c > 0 chosen with the program, before every input; reason: the uniform reading of the O(·) in the exponent
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Lemma 4.4, p. 15

import Definitions.Def_LatticeAvgPrec_OneVector_Cost
open Matrix

namespace LatticeAvgPrec.OneVector

/-- **Lemma 4.4** (Basis reduction with conditioning bounds; STOC 2027 submission #1574, p.15). Let
`E ∈ ℤ^{k×k}` be nonsingular with `‖E‖₂, ‖E⁻¹‖₂ ≤ 2^h` and `h ≥ k`. In deterministic `Õ(k^ω h)`
time, including input and output, one can compute `U ∈ GL_k(ℤ)`, the basis `Y = EU`, and positive
dyadic `ρ̃_i` such that, for the Gram–Schmidt lengths `ρ_i` of `Y`, `ρ̃_i ≤ ρ_i ≤ 4ρ̃_i`,
`‖Y_j‖₂ ≤ 2^{O(k)} ρ_i` (`j ≤ i`), `κ_col(Y) ≤ 2^{O(k)}`. Consequently
`‖Y_i‖₂ ≤ 2^{O(k)} λ_i(Eℤ^k)`. The matrix `U` has `Õ(h)`-bit entries.

**Formalization Note** The program receives `(h, E)`. Columns are indexed from `0`, so column `i`
is compared with `λ_{i+1}`. `ρ̃_i = num_i / 2^{ex_i}`. -/
theorem lemma_4_4 (ω : ℝ) (hω₁ : 2 < ω) (hω₂ : ω ≤ 3) (hM : MatMulAvailable ω) :
    ∃ (P : TimeSpaceMA.Program) (c : ℝ) (g : ℕ → ℕ → ℝ), 0 < c ∧ IsSubpoly g ∧
      ∀ (k h : ℕ) (E : Matrix (Fin k) (Fin k) ℤ), 1 ≤ k → E.det ≠ 0 → k ≤ h →
        specNorm (rmat E) ≤ (2 : ℝ) ^ h → specNorm (rmat E)⁻¹ ≤ (2 : ℝ) ^ h →
        SoftmaxAttnFD.DeterministicWithin P (TimeSpaceMA.memOf (natCode h ++ matCode E))
          (fun mem => ∃ (U Y : Matrix (Fin k) (Fin k) ℤ) (num : Fin k → ℤ) (ex : Fin k → ℕ),
            memHolds mem (matCode U ++ matCode Y ++ dyVecCode num ex) ∧
            IsUnit U.det ∧ Y = E * U ∧ (∀ i, 0 < num i) ∧
            (∀ (O R : Matrix (Fin k) (Fin k) ℝ), IsPosQR (rmat Y) O R →
              (∀ i, dyVal (num i) (ex i) ≤ R i i ∧ R i i ≤ 4 * dyVal (num i) (ex i)) ∧
              ∀ i j, j ≤ i → colNorm Y j ≤ (2 : ℝ) ^ (c * k) * R i i) ∧
            kappaCol (rmat Y) ≤ (2 : ℝ) ^ (c * k) ∧
            (∀ i : Fin k, colNorm Y i ≤ (2 : ℝ) ^ (c * k) * lam (lat E) ((i : ℕ) + 1)) ∧
            ∀ i j, (bits (U i j) : ℝ) ≤ g k h * h)
          (g k h * (k : ℝ) ^ ω * h) := by sorry

end LatticeAvgPrec.OneVector
