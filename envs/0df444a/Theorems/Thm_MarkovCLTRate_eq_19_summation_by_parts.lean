-- Prove2me | Theorems.Thm_MarkovCLTRate_eq_19_summation_by_parts
-- name    : MarkovCLTRate.eq_19_summation_by_parts
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:55.409268+00:00
-- url     : https://prove2.me/theorems/f27674ec-3054-49cb-982f-3ea29c560d83
-- title:
--   (19): summation by parts, $\|H_k\|_{op}\le Cq_k^{-1/2}$ and $O(1)$ boundary terms
-- statement:
--   In the setting of the proof of Theorem 3 with $\Sigma_\infty\succ0$, let $\Psi$ solve (16) with the bound (17), and for $h\in Lip_1$ let $H_k=V_k^{-1/2}A_{k,h}(\mathcal F_{k-1})V_k^{-1/2}$, $q_k=n-k+1$. There are $n_0$ and $C$ such that for all $n\ge n_0$ and $h\in Lip_1$:
--
--   1. $\|H_k\|_{op}\le Cq_k^{-1/2}$ for $k=1,\dots,n$;
--   2. $E\operatorname{Tr}(H_k\Gamma_k)=0$;
--   3. the summation-by-parts identity
--   $$
--   \sum_{k=1}^nE\operatorname{Tr}\big(H_k(E(\Sigma_k)-\Sigma_k)\big)=E\operatorname{Tr}(H_1\tilde\Psi_0)-E\operatorname{Tr}(H_n\tilde\Psi_n)+\sum_{k=2}^nE\operatorname{Tr}\big((H_k-H_{k-1})\tilde\Psi_{k-1}\big)\qquad(19)
--   $$
--   holds, with every trace integrable;
--   4. the two boundary terms of (19) are $O(1)$ uniformly over $h\in Lip_1$: $E|\operatorname{Tr}(H_1\tilde\Psi_0)|\le C$ and $E|\operatorname{Tr}(H_n\tilde\Psi_n)|\le C$.
--
--   **Formalization Note** $n_0$ and $C$ are chosen before $n$, $k$, $h$ and the path.
--
--   Differences from the source:
--   - reading: a state space S (general) → [MeasurableSpace.CountablyGenerated S]; reason: Meyn and Tweedie's standing assumption; the paper borrows their machinery (p.17) and the proof rests on their Chapters 15-17
--   - generalization: p = 2 + β (item 1 of Theorem 3), repeated with p = 4 on p.22 (item 2) → one exponent 2 < p ≤ 4 in ProofSetting, with ‖g‖^p ≤ C_r𝒱 and ‖V_r‖ ≤ C(1 + 𝒱^{1/p}); reason: the same argument covers both; p = 2 + β and p = 4 are the two instances, so the statement specializes to the page's
--   - reading: the estimate inside the proof, where V_k^{−1/2} is used → for all n ≥ n₀ (∃ n₀ before n); reason: (14), which makes V_k invertible, holds only for all sufficiently large n (p.19); for small n, V_1 can be singular (paper.md R6: n = 1, d = 2, deterministic X_0)
--   - generalization: the two boundary terms in (19) are O(1), i.e. |E Tr(H_1Ψ̃_0)|, |E Tr(H_nΨ̃_n)| ≤ C → E|Tr(H_1Ψ̃_0)| ≤ C and E|Tr(H_nΨ̃_n)| ≤ C, and integrability of every trace in (19); reason: the absolute first moment bounds the absolute value of the expectation; stating it (and integrability) excludes expectations defaulting to 0
--   - generalization: (19) for the solution Ψ of (16) with (17) → every componentwise solution Ψ of (16) with the bound (17), taken as a hypothesis; reason: the derivation uses only (16), (17) and the Markov property; the solution of p.20 is one such Ψ, so the statement specializes to the page’s
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, proof of Theorem 3, pp.20–21, E Tr(H_kΓ_k) = 0, (19), ‖H_k‖ ≤ Cq_k^{−1/2}, boundary terms

import Mathlib
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_MartingaleCLT
import Definitions.Def_MarkovCLTRate_GeneralChain
import Definitions.Def_MarkovCLTRate_ChainFunctionals

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **Summation by parts, (19)**, arXiv:2401.15719v5, proof of Theorem 3, pp.20–21. In the setting
of the proof with `Σ_∞ ≻ 0`, let `Ψ` solve (16) with the bound (17), and for `h ∈ Lip_1` let
`H_k = V_k^{−1/2} A_{k,h}(𝓕_{k−1}) V_k^{−1/2}`. Then for all sufficiently large `n`:
1. `‖H_k‖_op ≤ C q_k^{−1/2}`, `q_k = n − k + 1` (the Stein bound of Theorem 1 and (14));
2. `E Tr(H_k Γ_k) = 0`, because `H_k` is `𝓕_{k−1}`-measurable and `E[Γ_k | 𝓕_{k−1}] = 0`;
3. `Σ_{k=1}^n E Tr(H_k(E(Σ_k) − Σ_k)) = E Tr(H_1 Ψ̃_0) − E Tr(H_n Ψ̃_n)
   + Σ_{k=2}^n E Tr((H_k − H_{k−1}) Ψ̃_{k−1})`   (19);
4. the two boundary terms in (19) are `O(1)`, uniformly over `h ∈ Lip_1`.

**Formalization Note.** `n₀` and `C` are chosen before `n`, `k`, `h` and the path, so the bounds are
uniform over `Lip_1`. Every trace in items 2 and 3 is asserted integrable, so no expectation takes
Lean's default value. Item 4 bounds `E|Tr(·)|`, which bounds `|E Tr(·)|`. -/
theorem eq_19_summation_by_parts {S : Type*} [MeasurableSpace S]
    [MeasurableSpace.CountablyGenerated S] {d : ℕ}
    (P : Kernel S S) [IsMarkovKernel P] (π η : Measure S) (lyap : S → ℝ) (lam L : ℝ)
    (r : S → Vec d) (p Cr : ℝ) (V : S → Vec d)
    (hset : ProofSetting P π η lyap lam L r p Cr V) (hSig : (sigmaInf P π V).PosDef)
    (Ψ : S → Mat d) (hΨ : IsMatPoissonSolution P (Bmat P π V) Ψ)
    (hΨgrowth : ∃ C : ℝ, ∀ x, opNorm (Ψ x) ≤ C * (1 + lyap x ^ (2 / p))) :
    ∃ (n₀ : ℕ) (C : ℝ), ∀ n : ℕ, n₀ ≤ n → ∀ h : Vec d → ℝ, LipschitzWith 1 h →
      (∀ k ∈ Finset.Icc 1 n, ∀ ω : ℕ → S,
        opNorm (Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n k h ω)
          ≤ C * ((n : ℝ) - k + 1) ^ (-(1 : ℝ) / 2)) ∧
      (∀ k ∈ Finset.Icc 1 n,
        Integrable (fun ω => Matrix.trace
          (Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n k h ω
            * gammaMat (MarkovChainCLT.chainMeasure P η) Ψ k ω))
          (MarkovChainCLT.chainMeasure P η) ∧
        ∫ ω, Matrix.trace
          (Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n k h ω
            * gammaMat (MarkovChainCLT.chainMeasure P η) Ψ k ω)
          ∂(MarkovChainCLT.chainMeasure P η) = 0) ∧
      (∀ k ∈ Finset.Icc 1 n,
        Integrable (fun ω => Matrix.trace
          (Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n k h ω
            * (expCov (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) k
              - condCov (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) k ω)))
          (MarkovChainCLT.chainMeasure P η) ∧
        Integrable (fun ω => Matrix.trace
          (Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n k h ω
            * psiTilde (MarkovChainCLT.chainMeasure P η) Ψ k ω))
          (MarkovChainCLT.chainMeasure P η) ∧
        Integrable (fun ω => Matrix.trace
          (Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n k h ω
            * psiTilde (MarkovChainCLT.chainMeasure P η) Ψ (k - 1) ω))
          (MarkovChainCLT.chainMeasure P η)) ∧
      (∑ k ∈ Finset.Icc 1 n, ∫ ω, Matrix.trace
          (Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n k h ω
            * (expCov (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) k
              - condCov (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) k ω))
          ∂(MarkovChainCLT.chainMeasure P η)
        = ∫ ω, Matrix.trace
            (Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n 1 h ω
              * psiTilde (MarkovChainCLT.chainMeasure P η) Ψ 0 ω)
            ∂(MarkovChainCLT.chainMeasure P η)
          - ∫ ω, Matrix.trace
            (Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n n h ω
              * psiTilde (MarkovChainCLT.chainMeasure P η) Ψ n ω)
            ∂(MarkovChainCLT.chainMeasure P η)
          + ∑ k ∈ Finset.Icc 2 n, ∫ ω, Matrix.trace
            ((Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n k h ω
              - Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n (k - 1)
                  h ω)
              * psiTilde (MarkovChainCLT.chainMeasure P η) Ψ (k - 1) ω)
            ∂(MarkovChainCLT.chainMeasure P η)) ∧
      (∫⁻ ω, ENNReal.ofReal |Matrix.trace
          (Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n 1 h ω
            * psiTilde (MarkovChainCLT.chainMeasure P η) Ψ 0 ω)|
          ∂(MarkovChainCLT.chainMeasure P η) ≤ ENNReal.ofReal C ∧
       ∫⁻ ω, ENNReal.ofReal |Matrix.trace
          (Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n n h ω
            * psiTilde (MarkovChainCLT.chainMeasure P η) Ψ n ω)|
          ∂(MarkovChainCLT.chainMeasure P η) ≤ ENNReal.ofReal C) := by sorry

end MarkovCLTRate
