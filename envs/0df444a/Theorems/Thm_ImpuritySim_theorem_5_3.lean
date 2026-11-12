-- Prove2me | Theorems.Thm_ImpuritySim_theorem_5_3
-- name    : ImpuritySim.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:33:39.555539+00:00
-- url     : https://prove2.me/theorems/46b408f0-5984-4e94-97f9-8ea9bf8f44b3
-- title:
--   Theorem 5.3 — ground energy of every impurity model to additive error $\delta$ by one deterministic real-RAM program in time $\mathrm{poly}(n,\delta^{-1})$ (pinned-down version)
-- statement:
--   Let $H=H_0+H_{\mathrm{imp}}$ be a quantum impurity model (1.1) on $n$ fermionic modes,
--   $$H_0=\alpha I+\frac i4\sum_{j,k=1}^{2n}h_{jk}\gamma_j\gamma_k,\qquad H_{\mathrm{imp}}=\sum_{A\subseteq\{1,\dots,2m\},\ |A|\text{ even}}c_A\Gamma_A,$$
--   with $\alpha\in\mathbb R$, $h$ real antisymmetric and real coefficients $c_A$, so that $H_{\mathrm{imp}}$ is an arbitrary even Hermitian polynomial in $\gamma_1,\dots,\gamma_{2m}$. For any precision parameter $\delta$ there is a classical algorithm that estimates the ground energy of $H$ to additive error $\delta$ with runtime $\mathrm{poly}(n,\delta^{-1})$, under the standing assumptions $\|H\|=\mathrm{poly}(n)$, $\|h_{\mathrm{bath}}\|\le J=\mathrm{poly}(n)$ and $m=O(1)$.
--
--   Precisely (the operator-requested pinned-down statement): there is one admissible, deterministic program $P$ of the unit-cost real RAM such that for all $m,c\in\mathbb N$ there are $C,K\in\mathbb N$ with the following property. For every $n\ge 1$ with $n\ge m$, every $\alpha$, every real antisymmetric $h$ and every $(c_A)$ with
--   $$\|H\|\le c\,n^c\qquad\text{and}\qquad\|h_{\mathrm{bath}}\|\le c\,n^c,$$
--   and every $\delta>0$, the run of $P$ on input $(n,m,\delta,\alpha,h,c)$ has halted after $\lceil C(n+\delta^{-1})^K\rceil$ steps with an output $E$ satisfying
--   $$|E-\lambda_{\min}(H)|\le\delta.$$
--
--   This improves the quasipolynomial-time algorithm of Bravyi and Gosset to polynomial time and places the ground-state problem for impurity models in classical polynomial time.
--
--   **Formalization Note** The real RAM has $+,-,\times,\div$, comparisons, integer pointers and rational literals, and no square root, floor, exponential, logarithm or eigen-decomposition instruction. $\|\cdot\|$ is the spectral norm; $\lambda_{\min}$ is the Rayleigh infimum, equal to the least eigenvalue of the Hermitian $H$.
--
--   Differences from the source:
--   - reading: "a classical algorithm … with runtime poly(n, δ^{−1})" → one Admissible, Deterministic program of the published unit-cost arithmetic real RAM SubsetConvFPRAS (no eigen-decomposition, √ or floor instruction); reason: the paper names no model and its inputs are real; of the two standard real-RAM readings, the one without an eigensolver is the stronger theorem
--   - reading: "∥H∥ = poly(n)", "∥h_bath∥ ≤ J = poly(n)" (p.12), "m = O(1)" (p.4) → promises specNorm H ≤ c·n^c and specNorm h_bath ≤ c·n^c; C and K depend only on (m, c); reason: the explicit quantification of the standing assumptions
--   - generalization: an algorithm for each constant impurity size m → one program for all m and c, reading m from its input; only C, K depend on (m, c); reason: specializes to every fixed m
--   - encoding: runtime poly(n, δ^{−1}), "for any precision parameter δ" → halted with output after ⌈C·(n + δ^{−1})^K⌉ steps, for every real δ > 0; reason: the halted state stutters, so the output after that many steps is final; the step count depends on n and δ only
--   - encoding: the input (n, m, δ, α, h, H_imp) → integer memory I0 = n, I1 = m; real memory M0 = δ, M1 = α, M(2 + 2n·j + k) = h_{jk}, M(2 + 4n² + Σ_{a∈A} 2^a) = c_A (start); reason: a fixed input layout; the cells are distinct
--   - encoding: H_imp "a sum of even-degree products" of γ_1, …, γ_{2m} → Σ_{A ⊆ Fin (2m), |A| even} c_A Γ_A with real c_A; reason: the Γ_A are a basis and Hermitian, so every even Hermitian H_imp has exactly one such expansion
--   - encoding: Majorana operators γ_1, …, γ_{2n} (Jordan–Wigner, p.4) → the published Jordan–Wigner generators FermiCap.Gaussian.majorana, 0-based; reason: the paper's representation; λ_min does not depend on the representation of the CAR
--   - encoding: the ground energy of H → the Rayleigh infimum groundEnergy H; reason: equals λ_min for the Hermitian H
--   - generalization: n fermionic modes with a constant-size impurity (n ≥ 1, m ≥ 1 implicit) → every n ≥ 1 and every m with m ≤ n, including m = 0; reason: contains every instance of the paper (n = 0 is excluded: there the budget ⌈C(n + δ^{−1})^K⌉ is one step for large δ)
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Theorem 5.3, p.27; model (1.1), p.4; standing assumptions (2.12), p.12; m = O(1), p.4

import Mathlib
import Definitions.Def_ImpuritySim_Model
import Definitions.Def_ImpuritySim_Machine

open Matrix

namespace ImpuritySim

/-- **Theorem 5.3 (Efficient classical ground energy estimation)**, p.27, of J. Jiang, N. Ju,
O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation of quantum
impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2); model (1.1), p.4;
standing assumptions (2.12), p.12. Operator-requested pinned-down version.

Let `H = H0 + H_imp` be a quantum impurity model (1.1) on `n` fermionic modes:
`H0 = αI + (i/4) Σ_{j,k=1}^{2n} h_{jk} γ_j γ_k` with `α ∈ ℝ`, `h` real antisymmetric, and
`H_imp = Σ_{A ⊆ [2m], |A| even} c_A Γ_A` an arbitrary even Hermitian polynomial in
`γ_1, …, γ_{2m}`. There is one deterministic real-RAM program `P` such that for all `m, c ∈ ℕ`
there are `C, K` with: for every `n ≥ 1` with `n ≥ m`, every such `α, h, c_A` with `‖H‖ ≤ c·n^c` and
`‖h_bath‖ ≤ c·n^c`, and every precision `δ > 0`, the run of `P` on input `(n, m, δ, α, h, c_A)` has
halted after `⌈C (n + δ⁻¹)^K⌉` steps with an output `E` satisfying `|E − λ_min(H)| ≤ δ`.

**Formalization Note.**
* The machine is the published `SubsetConvFPRAS` unit-cost real RAM (`+ − × ÷`, comparisons,
  integer pointers and memory, rational literals); `P` is `Admissible` and `Deterministic` (no coin,
  no oracle). There is no square root, floor, exponential, logarithm or eigen-decomposition
  instruction.
* `n ≥ 1` (a system of `n` fermionic modes; at `n = 0` with `δ` large the budget
  `⌈C(n + δ⁻¹)^K⌉` would be a single step, which no program solving `n ≥ 1` can meet).
* One program serves every `m`, `c` and `n`; `m` is read from the input; only `C, K` depend on
  `(m, c)` ("`m = O(1)`", "`‖H‖ = poly(n)`", "`J = poly(n)`").
* Input layout: `start` (`I 0 = n`, `I 1 = m`; `M 0 = δ`, `M 1 = α`, `M (2 + 2n·j + k) = h_{jk}`,
  `M (2 + 4n² + Σ_{a ∈ A} 2^a) = c_A`).
* `‖·‖` is the spectral norm (`specNorm`); `h_bath` is the principal submatrix of `h` on
  `γ_{2m+1}, …, γ_{2n}` (`hBath`); the ground energy is the Rayleigh infimum (`groundEnergy`), which
  is `λ_min(H)` for the Hermitian `H`.
* The step bound depends on `n` and `δ` only, for every `δ > 0`; after `halt` the state stutters,
  so the output after that many steps is the final output. -/
theorem theorem_5_3 :
    ∃ P : SubsetConvFPRAS.Program, SubsetConvFPRAS.Admissible P ∧ SYKCavity.Deterministic P ∧
      ∀ m c : ℕ, ∃ C K : ℕ, ∀ (n : ℕ) (hn : 1 ≤ n) (hmn : m ≤ n) (α : ℝ)
        (h : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (cimp : Finset (Fin (2 * m)) → ℝ),
        hᵀ = -h →
        specNorm (Hmodel n m hmn α h cimp) ≤ (c : ℝ) * (n : ℝ) ^ c →
        specNorm (hBath n m h) ≤ (c : ℝ) * (n : ℝ) ^ c →
        ∀ δ : ℝ, 0 < δ →
          ∃ E : ℝ, outputAfter P n m δ α h cimp ⌈(C : ℝ) * ((n : ℝ) + δ⁻¹) ^ K⌉₊ = some E ∧
            |E - groundEnergy (Hmodel n m hmn α h cimp)| ≤ δ := by sorry

end ImpuritySim
