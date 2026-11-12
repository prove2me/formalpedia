-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_lemma_3_1
-- name    : LatticeAvgPrec.OneVector.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:51:14.940066+00:00
-- url     : https://prove2.me/theorems/36a4b7f9-fe4c-4644-9911-ae6b17034746
-- title:
--   Lemma 3.1 — Balanced equations from a Smith massager
-- statement:
--   Let $\Gamma\subseteq\mathbb Z^r$ be the lattice of a nonsingular $H\in\mathbb Z^{r\times r}$, and let $(S,F)$ be a nonempty ($m\ge1$) reduced Smith massager for $H$, $S=\operatorname{diag}(s_1,\dots,s_m)$. Put $D=\log_2\det\Gamma=\sum_j\log_2 s_j$. From $(S,F)$, in $\widetilde O(r(D+r))$ deterministic bit operations, one can construct integer matrices $K\in\mathbb Z^{q\times q}$ and $A\in\mathbb Z^{q\times r}$ such that, for some integer $t$,
--   $$q<3r,\qquad t\le \frac{D}{r+m}+2,\qquad |K_{ij}|,|A_{ij}|\le 2^t,$$
--   $$\Gamma=\{z\in\mathbb Z^r: -K^{-1}Az\in\mathbb Z^q\},\qquad |\det K|=2^D,$$
--   $$\|K^{-1}\|_2\le 3\sqrt q,\qquad \|K^{-1}A\|_2\le 2\sqrt{rq},$$
--   and the map $[K,A]:\mathbb Z^{q+r}\to\mathbb Z^q$ is onto.
--
--   These balanced equations replace the long modular conditions $F^Tz\in S\mathbb Z^m$ by short integer equations, which is what lets the embedding of Theorem 3.3 work at average precision.
--
--   **Formalization Note** The input is the code of $(s,F)$ only; $H$ is any basis for which $(S,F)$ is a reduced massager. Logarithms are base 2, as everywhere in the paper.
--
--   Differences from the source:
--   - reading: costs measured in bit operations, with quasi-linear scalar integer arithmetic; deterministic cost → bit cost of a program of the published logarithmic-cost RAM (TimeSpaceMA_RAM with the cost layer SoftmaxAttnFD_Machine): each instruction costs 1 plus the bit sizes of every address and value it touches; DeterministicWithin: coin-free, halts within the bound on every tape with a correct output; reason: the paper names no machine; the matrix-multiplication hypothesis MatMulAvailable is stated in the same model, so the reading neither adds nor removes power
--   - reading: Õ(f) suppresses subpolynomial factors in the dimension and precision parameters (p.4) → g(r, ⌈D⌉)·f with g subpolynomial (IsSubpoly: for every ε > 0, g x y ≤ C_ε (x + y + 2)^ε), g chosen with the program before every input; reason: the p.4 convention made uniform; a factor fixed before the input is the honest reading of Õ
--   - encoding: binary input and output → integers coded one bit per memory cell (natCode / intCode, self-delimiting), vectors and matrices with their dimensions first, input from cell 0 (memOf), output held from cell 0 (memHolds); reason: keeps the bit count of the binary representation; the codes are prefix-free, so the output is read unambiguously
--   - reading: t appears in the display without a binder → ∃ t : ℕ with t ≤ D/(r+m) + 2 and |K_ij|, |A_ij| ≤ 2^t; reason: the proof's digit width Q = 2^t; t is otherwise free
--   - encoding: (S, F) a reduced Smith massager for a basis of Γ ⊆ ℤ^r → Γ = Λ(H) for a nonsingular H ∈ ℤ^{r×r} with IsReducedSmithMassager H s F, H universally quantified and not part of the input; reason: a basis of a full-rank sublattice of ℤ^r is a nonsingular r×r integer matrix; the algorithm reads only (S, F)
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Lemma 3.1, pp. 9–10

import Definitions.Def_LatticeAvgPrec_OneVector_Cost
open Matrix

namespace LatticeAvgPrec.OneVector

/-- **Lemma 3.1** (Balanced equations from a Smith massager; STOC 2027 submission #1574, pp.9–10).
Let `(S, F)` be a nonempty reduced Smith massager for a basis `H` of `Γ ⊆ ℤ^r`,
`S = diag(s_1, …, s_m)`, and `D = log det Γ = Σ_j log s_j`. In `Õ(r(D + r))` bit operations one
can construct `K ∈ ℤ^{q×q}`, `A ∈ ℤ^{q×r}` with `q < 3r`, `t ≤ D/(r+m) + 2`,
`|K_ij|, |A_ij| ≤ 2^t`, `Γ = {z ∈ ℤ^r : −K⁻¹Az ∈ ℤ^q}`, `|det K| = 2^D`, `‖K⁻¹‖₂ ≤ 3√q`,
`‖K⁻¹A‖₂ ≤ 2√(rq)`, and `[K, A] : ℤ^{q+r} → ℤ^q` onto. -/
theorem lemma_3_1 :
    ∃ (P : TimeSpaceMA.Program) (g : ℕ → ℕ → ℝ), IsSubpoly g ∧
      ∀ (r m : ℕ) (H : Matrix (Fin r) (Fin r) ℤ) (s : Fin m → ℕ) (F : Matrix (Fin r) (Fin m) ℤ),
        H.det ≠ 0 → 1 ≤ m → IsReducedSmithMassager H s F →
        SoftmaxAttnFD.DeterministicWithin P
          (TimeSpaceMA.memOf (vecCode (fun j => (s j : ℤ)) ++ matCode F))
          (fun mem => ∃ (q : ℕ) (K : Matrix (Fin q) (Fin q) ℤ) (A : Matrix (Fin q) (Fin r) ℤ),
            memHolds mem (matCode K ++ matCode A) ∧
            q < 3 * r ∧
            (∃ t : ℕ, (t : ℝ) ≤ (∑ j, Real.logb 2 (s j)) / ((r : ℝ) + m) + 2 ∧
              (∀ i j, |K i j| ≤ 2 ^ t) ∧ ∀ i j, |A i j| ≤ 2 ^ t) ∧
            lat H = {z : Fin r → ℤ | ∃ a : Fin q → ℤ,
              (rmat K)⁻¹ *ᵥ (-(rmat A *ᵥ fun i => (z i : ℝ))) = fun i => (a i : ℝ)} ∧
            |(K.det : ℝ)| = (2 : ℝ) ^ (∑ j, Real.logb 2 (s j)) ∧
            specNorm (rmat K)⁻¹ ≤ 3 * Real.sqrt q ∧
            specNorm ((rmat K)⁻¹ * rmat A) ≤ 2 * Real.sqrt ((r : ℝ) * q) ∧
            ∀ w : Fin q → ℤ, ∃ (a : Fin q → ℤ) (z : Fin r → ℤ), K *ᵥ a + A *ᵥ z = w)
          (g r ⌈∑ j, Real.logb 2 (s j)⌉₊ * r * ((∑ j, Real.logb 2 (s j)) + r)) := by sorry

end LatticeAvgPrec.OneVector
