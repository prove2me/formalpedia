-- Prove2me | Theorems.Thm_HarrisonReimanRBM_Orthant_corollary_1_markov
-- name    : HarrisonReimanRBM.Orthant.corollary_1_markov
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T19:01:01.482261+00:00
-- url     : https://prove2.me/theorems/aaa75e6d-7ff0-4b5a-a995-df9760e27ea7
-- title:
--   Corollary 1(c) — $Z=\phi(X)$ is a time-homogeneous Markov process
-- statement:
--   Let $K\ge1$, let $A$ be a $K\times K$ covariance matrix (symmetric and nonnegative definite), $b\in\mathbb R^K$, and let $Q$ be a nonnegative $K\times K$ matrix with zeros on the diagonal and spectral radius strictly less than unity; $S=\mathbb R^K_+$. There is a family $(\kappa_t)_{t}$ of Markov transition kernels on $\mathbb R^K$, depending only on $(Q,A,b)$, with the following property.
--
--   Let $(\Omega,\mathcal F,P)$ be any probability space carrying a $K$-dimensional Brownian motion $X$ with covariance matrix $A$, drift vector $b$ and $X(0)\in S$ almost surely, $X(0)$ independent of the increments of $X$. Let $\mathcal F_t=\mathcal F(X(s);0\le s\le t)$, and let $Y=\psi(X)$, $Z=\phi(X)$ on the set where $X\in C_S$, with $Y(t)=Z(t)=0$ for all $t\ge0$ on the exceptional set. Then $Z$ is a Markov process with respect to $(\mathcal F_t)$ with stationary transition probabilities $\kappa$: for all $s,t\ge0$ and Borel $B\subseteq\mathbb R^K$,
--   $$P\big[Z(s+t)\in B\,\big|\,\mathcal F_s\big]=\kappa_t(Z(s),B)\quad\text{almost surely}.$$
--
--   This is part (c) of Corollary 1 of Harrison and Reiman; parts (a) (adaptedness) and (b) (pathwise existence and uniqueness of $(Y,Z)$) are proved separately in the reduction of `HarrisonReimanRBM.Orthant.corollary_1`.
--
--   **Formalization Note** The conventions are exactly those of `HarrisonReimanRBM.Orthant.corollary_1`: the kernel family is quantified before the probability space, the Brownian motion and the initial law, so it depends on $(Q,A,b)$ alone and not on $s$ (stationarity). The filtration is the uncompleted natural filtration of $X$. The conditional probability is the conditional expectation of the indicator of $\{Z(s+t)\in B\}$. Brownian motion with a random initial state and the processes $Y,Z$ are the definitions of `HarrisonReimanRBM.Orthant.Process`.
-- source:
--   Harrison & Reiman, Reflected Brownian Motion on an Orthant, Ann. Probab. 9(2) (1981), p. 305, Corollary 1 (c), with the construction of Z in the preceding paragraph

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_HarrisonReimanRBM_Orthant_Basic
import Definitions.Def_HarrisonReimanRBM_Orthant_Process

namespace HarrisonReimanRBM.Orthant

open MeasureTheory ProbabilityTheory Reiman84.QueueLength

/-- Corollary 1(c), p. 305. Fix `K ≥ 1`, `Q` as in §1, a covariance matrix `A` (symmetric,
nonnegative definite) and a drift vector `b`. There is a family `κ = (κ_t)` of Markov kernels on
`ℝ^K`, depending only on `(Q, A, b)`, such that for every probability space `(Ω, 𝓕, P)`, every
Brownian motion `X` with covariance `A`, drift `b`, `X(0) ∈ S` a.s. and `X(0)` independent of
the increments, and `Y = ψ(X)`, `Z = φ(X)` (set to `0` off `{X ∈ C_S}`), the process `Z` is a
Markov process with respect to `𝓕ₜ = 𝓕(X(s); 0 ≤ s ≤ t)` with stationary transition
probabilities `κ`: `P[Z(s + t) ∈ B | 𝓕ₛ] = κ_t(Z(s), B)` almost surely, for all `s, t ≥ 0` and
Borel `B`. -/
theorem corollary_1_markov {K : ℕ} (hK : 0 < K) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ : IsReflectionMatrix Q) (A : Matrix (Fin K) (Fin K) ℝ) (hA : A.PosSemidef)
    (b : Fin K → ℝ) :
    ∃ κ : ℝ → Kernel (Fin K → ℝ) (Fin K → ℝ), (∀ t, IsMarkovKernel (κ t)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X Y Z : Ω → ℝ → Fin K → ℝ),
        IsBMFrom b A P X → IsRBMConstruction Q X Y Z →
        ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ B : Set (Fin K → ℝ), MeasurableSet B →
          P[Set.indicator {ω | Z ω (s + t) ∈ B} (fun _ => (1 : ℝ)) | naturalFiltration X s]
            =ᵐ[P] fun ω => (κ t (Z ω s) B).toReal := by sorry

end HarrisonReimanRBM.Orthant
