-- Prove2me | Theorems.Thm_LogSobolevMC_Metropolis_lemma_3_2
-- name    : LogSobolevMC.Metropolis.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:03.446306+00:00
-- url     : https://prove2.me/theorems/715d56c9-cd5b-49fc-99fe-b652ffc60537
-- title:
--   Lemma 3.2, p. 716 — the product chain (2.9)–(2.10) has λ = (1/d) minᵢ λᵢ and α = (1/d) minᵢ αᵢ
-- statement:
--   Let $(K_i,\pi_i)$, $i=1,\dots,d$ ($d\ge 1$), be Markov chains on finite sets $\mathcal X_i$, each with a positive invariant probability $\pi_i$, spectral gap $\lambda_i$ and log-Sobolev constant $\alpha_i$. On $\mathcal X=\prod_{i=1}^d\mathcal X_i$ consider the product chain (2.9), which picks a coordinate $i$ uniformly at random and moves it according to $K_i$,
--
--   $$K(x,y)=\frac1d\sum_{i=1}^d\delta(x_1,y_1)\cdots\delta(x_{i-1},y_{i-1})K_i(x_i,y_i)\delta(x_{i+1},y_{i+1})\cdots\delta(x_d,y_d),$$
--
--   with the product measure $\pi(x)=\prod_{i=1}^d\pi_i(x_i)$ (2.10). Then
--
--   $$\lambda=\frac1d\min_i\lambda_i,\qquad \alpha=\frac1d\min_i\alpha_i.$$
--
--   The spectral gap and the log-Sobolev constant tensorize in the same way; this is what makes products a source of chains with explicitly known log-Sobolev constants.
--
--   **Formalization Note** The product chain is the published `MarkovMixing.productChain`. Each $\mathcal X_i$ is assumed to have at least two points: on a one-point factor $\lambda_i$ and $\alpha_i$ are infima over an empty set, which Lean evaluates to $0$ rather than $+\infty$, and the identity would fail. No irreducibility or reversibility is assumed.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 716, Lemma 3.2 (product chain of p. 713, (2.9)–(2.10))

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Metropolis_Setting

namespace LogSobolevMC.Metropolis

/-- Lemma 3.2, p. 716: the product chain (2.9) of chains `(Kᵢ, πᵢ)`, `i = 1, …, d`, with
the product measure (2.10) has spectral gap `λ = (1/d) minᵢ λᵢ` and log-Sobolev constant
`α = (1/d) minᵢ αᵢ`. Each factor space has at least two points (so that `λᵢ`, `αᵢ` are
infima over a nonempty set). -/
theorem lemma_3_2 (d : ℕ) (hd : 1 ≤ d) {W : Fin d → Type*}
    [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)] [∀ i, Nontrivial (W i)]
    (Kfam : ∀ i, Matrix (W i) (W i) ℝ) (πfam : ∀ i, W i → ℝ)
    (hK : ∀ i, MarkovMixing.IsStochastic (Kfam i))
    (hπ : ∀ i, MarkovMixing.IsStationary (Kfam i) (πfam i))
    (hπpos : ∀ i x, 0 < πfam i x) :
    LogSobolevMC.ChiSquare.gap (MarkovMixing.productChain Kfam) (fun x => ∏ i, πfam i (x i)) =
        (1 / (d : ℝ)) * ⨅ i, LogSobolevMC.ChiSquare.gap (Kfam i) (πfam i) ∧
    LogSobolevMC.ChiSquare.logSobolev (MarkovMixing.productChain Kfam) (fun x => ∏ i, πfam i (x i)) =
        (1 / (d : ℝ)) * ⨅ i, LogSobolevMC.ChiSquare.logSobolev (Kfam i) (πfam i) := by sorry

end LogSobolevMC.Metropolis
