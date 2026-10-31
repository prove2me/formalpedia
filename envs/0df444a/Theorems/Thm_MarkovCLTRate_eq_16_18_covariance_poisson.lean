-- Prove2me | Theorems.Thm_MarkovCLTRate_eq_16_18_covariance_poisson
-- name    : MarkovCLTRate.eq_16_18_covariance_poisson
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:06.126323+00:00
-- url     : https://prove2.me/theorems/21ec4a26-f015-4a88-9ce1-d096ff892f22
-- title:
--   (16)–(18): the covariance Poisson equation and $E(\Sigma_k)-\Sigma_k=\tilde\Psi_{k-1}-\tilde\Psi_k+\Gamma_k$
-- statement:
--   In the setting of the proof of Theorem 3 ($b=2/p$), let $B(x)=\Sigma_\infty-v(x)$. Then:
--
--   1. $\pi(B)=0$;
--   2. the matrix-valued Poisson equation $\Psi-P\Psi=B$ (16) has a componentwise solution with $\|\Psi(x)\|_{op}\le C(1+\mathcal V(x)^b)$; $\quad(17)$
--   3. for every such solution, with $\tilde\Psi_k=\Psi(X_k)-E[\Psi(X_k)]$ and $\Gamma_k=\Psi(X_k)-E[\Psi(X_k)\mid\mathcal F_{k-1}]$,
--   $$
--   E(\Sigma_k)-\Sigma_k=\tilde\Psi_{k-1}-\tilde\Psi_k+\Gamma_k\qquad(18)
--   $$
--   almost surely, for every $k\ge1$.
--
--   (18) turns the covariance-interaction term of Theorem 1 into telescoping terms plus martingale differences.
--
--   **Formalization Note** $\pi(B)$ is the entrywise $\pi$-integral. The centering in $\tilde\Psi_k$ is time dependent because $X_0\not\sim\pi$ in general.
--
--   Differences from the source:
--   - reading: a state space S (general) → [MeasurableSpace.CountablyGenerated S]; reason: Meyn and Tweedie's standing assumption; the paper borrows their machinery (p.17) and the proof rests on their Chapters 15-17
--   - generalization: p = 2 + β (item 1 of Theorem 3), repeated with p = 4 on p.22 (item 2) → one exponent 2 < p ≤ 4 in ProofSetting, with ‖g‖^p ≤ C_r𝒱 and ‖V_r‖ ≤ C(1 + 𝒱^{1/p}); reason: the same argument covers both; p = 2 + β and p = 4 are the two instances, so the statement specializes to the page's
--   - generalization: (18) for the solution Ψ of (16) with (17) → (18) for every componentwise solution Ψ with the bound (17); reason: the derivation uses only (16), the bound and the Markov property, so it holds for each such Ψ, including the one of item 2
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, proof of Theorem 3, p.20, B, (16), (17), (18)

import Mathlib
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_MartingaleCLT
import Definitions.Def_MarkovCLTRate_GeneralChain
import Definitions.Def_MarkovCLTRate_ChainFunctionals

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **The covariance Poisson equation, (16)–(18)**, arXiv:2401.15719v5, proof of Theorem 3, p.20.
In the setting of the proof (`b = 2/p`), let `B(x) = Σ_∞ − v(x)`. Then:
1. `π(B) = 0`;
2. the matrix-valued Poisson equation `Ψ − PΨ = B` (16) has a componentwise solution with
   `‖Ψ(x)‖_op ≤ C(1 + 𝒱(x)^b)`   (17);
3. for every such solution, with `Ψ̃_k = Ψ(X_k) − E[Ψ(X_k)]` and
   `Γ_k = Ψ(X_k) − E[Ψ(X_k) | 𝓕_{k−1}]`,
   `E(Σ_k) − Σ_k = Ψ̃_{k−1} − Ψ̃_k + Γ_k`   (18)
   almost surely, for every `k ≥ 1`.

**Formalization Note.** `π(B)` is the entrywise `π`-integral. The chain starts from `η`, so the
centering in `Ψ̃_k` is time dependent (p.20). (18) is stated for every solution with the growth
bound (17), not only the one constructed in item 2. -/
theorem eq_16_18_covariance_poisson {S : Type*} [MeasurableSpace S]
    [MeasurableSpace.CountablyGenerated S] {d : ℕ}
    (P : Kernel S S) [IsMarkovKernel P] (π η : Measure S) (lyap : S → ℝ) (lam L : ℝ)
    (r : S → Vec d) (p Cr : ℝ) (V : S → Vec d)
    (hset : ProofSetting P π η lyap lam L r p Cr V) :
    (∀ i j : Fin d, ∫ x, Bmat P π V x i j ∂π = 0) ∧
    (∃ Ψ : S → Mat d, IsMatPoissonSolution P (Bmat P π V) Ψ ∧
      ∃ C : ℝ, ∀ x, opNorm (Ψ x) ≤ C * (1 + lyap x ^ (2 / p))) ∧
    ∀ Ψ : S → Mat d, IsMatPoissonSolution P (Bmat P π V) Ψ →
      (∃ C : ℝ, ∀ x, opNorm (Ψ x) ≤ C * (1 + lyap x ^ (2 / p))) →
      ∀ k : ℕ, 1 ≤ k →
        (fun ω => expCov (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) k
            - condCov (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) k ω)
          =ᵐ[MarkovChainCLT.chainMeasure P η]
        fun ω => psiTilde (MarkovChainCLT.chainMeasure P η) Ψ (k - 1) ω
            - psiTilde (MarkovChainCLT.chainMeasure P η) Ψ k ω
            + gammaMat (MarkovChainCLT.chainMeasure P η) Ψ k ω := by sorry

end MarkovCLTRate
