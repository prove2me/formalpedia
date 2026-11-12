-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_lemma_A_1
-- name    : LatticeAvgPrec.OneVector.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:51:11.956682+00:00
-- url     : https://prove2.me/theorems/4a99286a-20a8-4d54-ae69-0e4f68781879
-- title:
--   Lemma A.1 — Finite-precision QR [DDH07, §4.1]
-- statement:
--   Let $\omega$ be an available exponent, $2<\omega\le3$. Let $X\in\mathbb R^{d\times k}$ have full column rank, $1\le k\le d$, with $\|X\|_F,\|X^\dagger\|_F\le2^b$, $b\ge1$. For its positive thin QR factor $X=OR$ write $R=\Delta W$, $\Delta=\operatorname{diag}(R_{ii})$. Given $a\ge1$ and sufficiently accurate input — a dyadic matrix $\widehat X=N/2^p$ with
--   $$\|\widehat X-X\|_F\le 2^{-p},\qquad p=a+C\bigl(b+\lceil\log_2(2d)\rceil\bigr)$$
--   for one constant $C$ fixed in advance — a deterministic computation of $\widetilde O(d^\omega(b+a))$ bit operations returns a dyadic unitriangular $\widehat W$ (exact unit diagonal) and a dyadic $\widehat R$ with
--   $$\|\widehat W-W\|_F\le 2^{-a},\qquad \|\widehat R-R\|_2\le 2^{-a}.$$
--
--   This is the finite-precision QR step used twice in the proof of Lemma 4.4: to obtain the unitriangular factor that triangular size reduction acts on, and to obtain the Gram–Schmidt length estimates.
--
--   **Formalization Note** The program receives $a$, $b$ and the numerators $N$. Outputs are $\widehat W=N_W/2^{e_1}$ and $\widehat R=N_R/2^{e_2}$. The QR factor is unique; the conclusion is stated for every positive QR factorization.
--
--   Differences from the source:
--   - reading: costs measured in bit operations, with quasi-linear scalar integer arithmetic; deterministic cost → bit cost of a program of the published logarithmic-cost RAM (TimeSpaceMA_RAM with the cost layer SoftmaxAttnFD_Machine): each instruction costs 1 plus the bit sizes of every address and value it touches; DeterministicWithin: coin-free, halts within the bound on every tape with a correct output; reason: the paper names no machine; the matrix-multiplication hypothesis MatMulAvailable is stated in the same model, so the reading neither adds nor removes power
--   - reading: Õ(f) suppresses subpolynomial factors in the dimension and precision parameters (p.4) → g(d, a + b)·f with g subpolynomial (IsSubpoly: for every ε > 0, g x y ≤ C_ε (x + y + 2)^ε), g chosen with the program before every input; reason: the p.4 convention made uniform; a factor fixed before the input is the honest reading of Õ
--   - encoding: binary input and output → integers coded one bit per memory cell (natCode / intCode, self-delimiting), vectors and matrices with their dimensions first, input from cell 0 (memOf), output held from cell 0 (memHolds); reason: keeps the bit count of the binary representation; the codes are prefix-free, so the output is read unambiguously
--   - encoding: a fixed available matrix-multiplication exponent 2 < ω ≤ 3; multiplying order-n integer matrices with b-bit entries costs Õ(n^ω b) (pp.4, 9) → hypotheses 2 < ω ≤ 3 and MatMulAvailable ω (a coin-free RAM program multiplies such matrices within g₀(n,b)·n^ω·b, g₀ subpolynomial); reason: the paper's standing assumption stated as a hypothesis; ω = 3 satisfies it, so the statement is not vacuous
--   - reading: given a ≥ 1 and sufficiently accurate input → input (a, b, N) with ‖N/2^p − X‖_F ≤ 2^{−p}, p = a + C(b + ⌈log₂(2d)⌉), one constant C chosen with the program; reason: the proof: 'p = a + O(b + log(2d)) suffices'; the input precision is fixed to this p so that the input size stays within the cost bound; b is recoverable from (a, p, d) and is passed explicitly
--   - encoding: real a ≥ 1 and b ≥ 1 → natural numbers a, b ≥ 1; reason: rounding a and b up changes the cost by a factor at most 2 and only sharpens the accuracy
--   - encoding: implicit k ≥ 1 → 1 ≤ k; reason: an empty matrix has no QR factor to approximate; the cost bound covers only d ≥ 1
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Lemma A.1, p. 27

import Definitions.Def_LatticeAvgPrec_OneVector_Cost
open Matrix

namespace LatticeAvgPrec.OneVector

/-- **Lemma A.1** (Finite-precision QR [DDH07, §4.1]; STOC 2027 submission #1574, p.27). Let
`X ∈ ℝ^{d×k}` have full column rank, `d ≥ k`, with `‖X‖_F, ‖X^†‖_F ≤ 2^b`, `b ≥ 1`. For its
positive thin QR factor write `R = ΔW`, `Δ = diag(R_ii)`. Given `a ≥ 1` and sufficiently accurate
input, a dyadic unitriangular `Ŵ` with `‖Ŵ − W‖_F ≤ 2^{−a}` is computable in `Õ(d^ω(b + a))` bit
operations; its unit diagonal is exact, and the same computation returns `R` to absolute operator
error `2^{−a}`.

**Formalization Note** "Sufficiently accurate input": the program receives `a`, `b` and a dyadic
matrix `N / 2^p` with `‖N/2^p − X‖_F ≤ 2^{−p}`, `p = a + C(b + ⌈log₂(2d)⌉)`, one constant `C`
fixed before all inputs. Outputs: `Ŵ = N_W / 2^{e₁}` and `R̂ = N_R / 2^{e₂}`. -/
theorem lemma_A_1 (ω : ℝ) (hω₁ : 2 < ω) (hω₂ : ω ≤ 3) (hM : MatMulAvailable ω) :
    ∃ (P : TimeSpaceMA.Program) (C : ℕ) (g : ℕ → ℕ → ℝ), IsSubpoly g ∧
      ∀ (d k a b : ℕ) (X : Matrix (Fin d) (Fin k) ℝ), 1 ≤ k → k ≤ d → 1 ≤ a → 1 ≤ b →
        X.rank = k → frob X ≤ (2 : ℝ) ^ b → frob (pinv X) ≤ (2 : ℝ) ^ b →
        ∀ N : Matrix (Fin d) (Fin k) ℤ,
          frob (dyMat N (a + C * (b + Nat.clog 2 (2 * d))) - X) ≤
            (2 : ℝ) ^ (-((a + C * (b + Nat.clog 2 (2 * d)) : ℕ) : ℝ)) →
          SoftmaxAttnFD.DeterministicWithin P
            (TimeSpaceMA.memOf (natCode a ++ natCode b ++ matCode N))
            (fun mem => ∃ (e₁ e₂ : ℕ) (Nw Nr : Matrix (Fin k) (Fin k) ℤ),
              memHolds mem (natCode e₁ ++ matCode Nw ++ natCode e₂ ++ matCode Nr) ∧
              IsUpperUnitri (dyMat Nw e₁) ∧
              ∀ (O : Matrix (Fin d) (Fin k) ℝ) (R : Matrix (Fin k) (Fin k) ℝ), IsPosQR X O R →
                frob (dyMat Nw e₁ - unitFactor R) ≤ (2 : ℝ) ^ (-(a : ℝ)) ∧
                specNorm (dyMat Nr e₂ - R) ≤ (2 : ℝ) ^ (-(a : ℝ)))
            (g d (a + b) * (d : ℝ) ^ ω * ((b : ℝ) + a)) := by sorry

end LatticeAvgPrec.OneVector
