-- Prove2me | Theorems.Thm_ImpuritySim_Supplement_theorem_6_8
-- name    : ImpuritySim.Supplement.theorem_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:33:39.314066+00:00
-- url     : https://prove2.me/theorems/c3d50aaf-97d6-4a16-bb86-613f671ba11c
-- title:
--   Theorem 6.8 — randomized real-RAM estimation of $\mathrm{Tr}(O\rho^{(\beta)})$ and $\mathrm{Tr}\,e^{-\beta H}$ in time $\mathrm{poly}(n,\beta,J,\epsilon^{-1})$ (pinned-down version)
-- statement:
--   Let $H=H_0+H_{\mathrm{imp}}$ be a quantum impurity model (1.1) on $n$ fermionic modes: $H_0=\alpha I+\frac i4\sum_{j,k=1}^{2n}h_{jk}\gamma_j\gamma_k$ with $\alpha\in\mathbb R$ and $h$ real antisymmetric, and $H_{\mathrm{imp}}=\sum_{A\subseteq[2m],\,|A|\text{ even}}c_A\Gamma_A$ an arbitrary even Hermitian polynomial in $\gamma_1,\dots,\gamma_{2m}$. Let $h_{\mathrm{bath}}$ be the bath block of $h$ and $J\ge\|h_{\mathrm{bath}}\|$. Let $O=\alpha_O\exp(\frac14\sum_{j,k}A_{jk}\gamma_j\gamma_k)$ be a Hermitian Gaussian observable with $\|O\|\le1$, and $\rho^{(\beta)}=e^{-\beta H}/\operatorname{Tr}e^{-\beta H}$.
--
--   There is one randomized program $P$ of the unit-cost real RAM with fair coins such that for all $m,c\in\mathbb N$ there are constants $C,K$ with the following property. For every $n\ge1$ with $m\le n$, every such $H$ with $\|H\|\le c\,n^c$, every $J\ge\|h_{\mathrm{bath}}\|$, every such $O$, every $\beta>0$ and every $0<\epsilon<1$, run $P$ for
--   $$B=\bigl\lceil C\,(n+\beta+J+\epsilon^{-1})^K\bigr\rceil$$
--   steps on the input $(n,m,\beta,\epsilon,J,\alpha,\alpha_O,h,A,c_A)$. Then, over the fair coins,
--   $$\Pr\Bigl[\bigl|\hat\mu-\operatorname{Tr}(O\rho^{(\beta)})\bigr|\le\epsilon\Bigr]\ge\frac23,\qquad \Pr\Bigl[\bigl|\hat Z-\operatorname{Tr}(e^{-\beta H})\bigr|\le\epsilon\operatorname{Tr}(e^{-\beta H})\Bigr]\ge\frac23,\qquad(6.37)$$
--   where $\hat\mu$ is the machine's output and $\hat Z$ the content of memory cell $M_{-1}$, and each event includes that the machine has halted within $B$ steps.
--
--   This extends the polynomial-time ground-energy algorithm of the mission's goal to thermal expectation values and the partition function at any temperature.
--
--   **Formalization Note** The machine has $+,-,\times,\div$, comparisons, integer pointers and memory, rational constants and fair coins, and no square root, exponential, logarithm, eigensolver or random-real instruction. Probabilities are fractions of the $2^B$ coin strings. $\|\cdot\|$ is the spectral norm.
--
--   Differences from the source:
--   - reading: "a randomized classical algorithm … with runtime poly(n, β, J, ϵ^{−1})" → one Admissible program without query instructions of the published unit-cost arithmetic real RAM SubsetConvFPRAS with fair coins (no √, exp, log, eigen-decomposition or random-real instruction); reason: the paper names no model and its inputs are real; this is the machine of the published goal, and the reading without extra primitives is the stronger theorem
--   - reading: "∥H∥ = poly(n)" (p.12), "m = O(1)" (p.4) → the promise specNorm H ≤ c·n^c with C, K depending only on (m, c); reason: the explicit quantification of the standing assumptions, as in the published goal
--   - generalization: "∥h_bath∥ ≤ J = poly(n)" (2.12) → any real J with specNorm h_bath ≤ J, given as input; reason: J appears in the step bound, so dropping J = poly(n) only adds instances; with J = poly(n) it specializes to the source
--   - generalization: an algorithm for each constant impurity size m → one program for all m and c, reading m from its input; reason: specializes to every fixed m
--   - generalization: "for any β > 0 and 0 < ϵ < 1, there is a randomized classical algorithm" → one program P, chosen before β, ϵ and the instance, reading β and ϵ from its input; reason: specializes to an algorithm for each fixed β and ϵ with the same runtime bound
--   - generalization: n fermionic modes with a constant-size impurity → every n ≥ 1 and every m ≤ n, including m = 0; reason: contains every instance of the paper (n = 0 is excluded, as in the published goal)
--   - encoding: runtime poly(n, β, J, ϵ^{−1}) → the run of B = ⌈C(n + β + J + ϵ^{−1})^K⌉ steps, each event requiring that the machine has halted within B steps; reason: the halted state stutters, so its outputs are final
--   - encoding: "Pr[…] ≥ 2/3" → 3·(number of coin strings in Fin B → Bool on which the event holds) ≥ 2·2^B; reason: probability over fair coins; a run of B steps reads at most B coins
--   - reading: "outputs estimates µ̂ and Ẑ" → one run yields µ̂ (output register) and Ẑ (memory cell M(−1) after halting); each of the two events of (6.37) has probability ≥ 2/3 separately; reason: as printed, the two bounds are separate
--   - encoding: the input (n, m, β, ϵ, J, α, O, h, H_imp) → integer memory I0 = n, I1 = m; real memory M0 = β, M1 = ϵ, M2 = J, M3 = α, M4 = Re α_O, M5 = Im α_O, h, Re A, Im A row by row from M6, then c_A at M(6 + 12n² + Σ_{a∈A} 2^a) (start68); reason: a fixed input layout; the cells are distinct
--   - encoding: "Gaussian observable O = α exp(¼ Σ A_jk γ_j γ_k) for some scalar α and antisymmetric A" (Definition 6.7) → α_O ∈ ℂ and A a complex 2n × 2n matrix with Aᵀ = −A, given as input; reason: the definition allows any scalar and any antisymmetric matrix
--   - encoding: H_imp "a sum of even-degree products" of γ_1, …, γ_{2m} → Σ_{A ⊆ Fin (2m), |A| even} c_A Γ_A with real c_A; reason: the Γ_A are a basis and Hermitian, so every even Hermitian H_imp has exactly one such expansion
--   - encoding: Majorana operators γ_1, …, γ_{2n} → the published Jordan–Wigner generators, 0-based; reason: the paper's representation (p.4)
--   - encoding: |µ̂ − Tr(Oρ^(β))| and Tr(e^{−βH}) → the complex modulus of µ̂ − Tr(Oρ^(β)), and the real part of Tr(e^{−βH}); reason: both traces are real (O Hermitian, e^{−βH} positive definite)
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Theorem 6.8, Eq. (6.37), and Definition 6.7, p.34; model (1.1), p.4; (2.12), p.12; proof pp.34–35 and App. C

import Mathlib
import Definitions.Def_ImpuritySim_Supplement_ThermalMachine
import Definitions.Def_WolfAreaLaw_thermalState

open Matrix

namespace ImpuritySim.Supplement

/-- **Theorem 6.8 (Efficient classical simulation of thermal states)**, p.34, of J. Jiang, N. Ju,
O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation of quantum
impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Eq. (6.37), with
model (1.1), p.4, standing assumptions (2.12), p.12, and Definition 6.7, p.34. Operator-requested
pinned-down version, in the machine model of the published goal (Theorem 5.3).

Let `H = H0 + H_imp` be a quantum impurity model (1.1) on `n` modes and `O` a Hermitian Gaussian
observable with `‖O‖ ≤ 1`. There is one randomized real-RAM program `P` such that for all `m, c ∈ ℕ`
there are `C, K` with: for every `n ≥ 1` with `m ≤ n`, every `α ∈ ℝ`, real antisymmetric `h` and real
`c_A` with `‖H‖ ≤ c·n^c`, every `J ≥ ‖h_bath‖`, every Gaussian `O = α_O exp(¼ Σ A_{jk} γ_j γ_k)`
(`A` antisymmetric) that is Hermitian with `‖O‖ ≤ 1`, every `β > 0` and every `0 < ϵ < 1`, after
`B = ⌈C (n + β + J + ϵ⁻¹)^K⌉` steps on input `(n, m, β, ϵ, J, α, α_O, h, A, c_A)`:
`Pr[halted ∧ |μ̂ − Tr(Oρ^(β))| ≤ ϵ] ≥ 2/3` and `Pr[halted ∧ |Ẑ − Tr e^{−βH}| ≤ ϵ Tr e^{−βH}] ≥ 2/3`,
over the fair coins, where `μ̂` is the output and `Ẑ` the final memory cell `M(−1)`.

**Formalization Note.**
* The machine is the published `SubsetConvFPRAS` unit-cost real RAM (`+ − × ÷`, comparisons,
  integer pointers and memory, rational literals, fair coins); `P` is `Admissible` and has no
  `query` instruction. There is no square root, exponential, logarithm, eigen-decomposition or
  random-real instruction.
* One program serves every `m`, `c`, `n`; only `C, K` depend on `(m, c)` ("`m = O(1)`",
  "`‖H‖ = poly(n)`" of (2.12)). `J` is an input with `‖h_bath‖ ≤ J`; it appears in the step bound.
* Probabilities are counts of coin strings `Fin B → Bool` (`SubsetConvFPRAS.tapeCount`): an event
  has probability `≥ 2/3` iff `3 · count ≥ 2 · 2^B`. The two events are bounded separately.
* `‖·‖` is the spectral norm (`specNorm`), `h_bath` the bath block (`hBath`), `ρ^(β)` the published
  `WolfAreaLaw.thermalState`; `Tr e^{−βH}` (real and positive) is compared through its real part,
  `Tr(Oρ^(β))` as a complex number. Input layout: `start68`. -/
theorem theorem_6_8 :
    ∃ P : SubsetConvFPRAS.Program, SubsetConvFPRAS.Admissible P ∧ NoQuery P ∧
      ∀ m c : ℕ, ∃ C K : ℕ, ∀ (n : ℕ) (hn : 1 ≤ n) (hmn : m ≤ n) (α : ℝ)
        (h : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (cimp : Finset (Fin (2 * m)) → ℝ),
        hᵀ = -h →
        specNorm (Hmodel n m hmn α h cimp) ≤ (c : ℝ) * (n : ℝ) ^ c →
        ∀ J : ℝ, specNorm (hBath n m h) ≤ J →
        ∀ (αO : ℂ) (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ), Aᵀ = -A →
        (gaussObs n αO A).IsHermitian → specNorm (gaussObs n αO A) ≤ 1 →
        ∀ β : ℝ, 0 < β → ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 →
          2 * 2 ^ ⌈(C : ℝ) * ((n : ℝ) + β + J + ϵ⁻¹) ^ K⌉₊ ≤
              3 * SubsetConvFPRAS.tapeCount P (fun _ => 0) (fun _ => 0)
                (start68 n m β ϵ J α αO h A cimp) ⌈(C : ℝ) * ((n : ℝ) + β + J + ϵ⁻¹) ^ K⌉₊
                (fun s => ∃ μ : ℝ, s.output = some μ ∧
                  ‖(μ : ℂ) - (gaussObs n αO A *
                    WolfAreaLaw.thermalState β (Hmodel n m hmn α h cimp)).trace‖ ≤ ϵ) ∧
            2 * 2 ^ ⌈(C : ℝ) * ((n : ℝ) + β + J + ϵ⁻¹) ^ K⌉₊ ≤
              3 * SubsetConvFPRAS.tapeCount P (fun _ => 0) (fun _ => 0)
                (start68 n m β ϵ J α αO h A cimp) ⌈(C : ℝ) * ((n : ℝ) + β + J + ϵ⁻¹) ^ K⌉₊
                (fun s => s.output.isSome ∧
                  |zHat s - (NormedSpace.exp (-(β : ℂ) • Hmodel n m hmn α h cimp)).trace.re| ≤
                    ϵ * (NormedSpace.exp (-(β : ℂ) • Hmodel n m hmn α h cimp)).trace.re) := by sorry

end ImpuritySim.Supplement
