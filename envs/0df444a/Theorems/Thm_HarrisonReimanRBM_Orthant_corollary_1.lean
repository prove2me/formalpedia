-- Prove2me | Theorems.Thm_HarrisonReimanRBM_Orthant_corollary_1
-- name    : HarrisonReimanRBM.Orthant.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:22:45.997098+00:00
-- url     : https://prove2.me/theorems/b0404faf-dfa2-4080-bebe-4afe43c3f301
-- title:
--   Corollary 1: $Y,Z$ are adapted, a.s. unique solutions of (1)–(4), and $Z$ is Markov with stationary transition probabilities
-- statement:
--   Let $K\ge1$, let $A$ be a $K\times K$ covariance matrix (symmetric and nonnegative definite), $b\in\mathbb R^K$, and let $Q$ be a nonnegative $K\times K$ matrix with zeros on the diagonal and spectral radius strictly less than unity; $S=\mathbb R^K_+$. There is a family $(\kappa_t)_{t}$ of Markov transition kernels on $\mathbb R^K$, depending only on $(Q,A,b)$, with the following property.
--
--   Let $(\Omega,\mathcal F,P)$ be any probability space carrying a $K$-dimensional Brownian motion $X$ with covariance matrix $A$, drift vector $b$ and $X(0)\in S$ almost surely, $X(0)$ independent of the increments of $X$. Let $\mathcal F_t=\mathcal F(X(s);0\le s\le t)$, and let $Y=\psi(X)$, $Z=\phi(X)$ on the set where $X\in C_S$ and $Y(t)=Z(t)=0$ for all $t\ge0$ on the exceptional set. Then:
--
--   1. **(a)** $Y(t)$ and $Z(t)$ are $\mathcal F_t$-measurable for each $t\ge0$;
--   2. **(b)** $Y$ and $Z$ satisfy (1)–(4),
--   $$Z(t)=X(t)+Y(t)(I-Q),\quad Z(t)\in S,\quad Y\text{ continuous, nondecreasing},\ Y(0)=0,\quad Y_j\text{ increases only when }Z_j=0,$$
--   almost surely, and any pair of processes $(Y',Z')$ that satisfies (1)–(4) almost surely agrees with $(Y,Z)$ at all times $t\ge0$ outside a single null set;
--   3. **(c)** $Z$ is a Markov process with stationary transition probabilities $\kappa$: for all $s,t\ge0$ and Borel $B\subseteq\mathbb R^K$,
--   $$P\big[Z(s+t)\in B\,\big|\,\mathcal F_s\big]=\kappa_t(Z(s),B)\quad\text{almost surely}.$$
--
--   This is the paper's construction of reflected Brownian motion on the orthant as a Markov process with continuous paths and state space $S$.
--
--   **Formalization Note** The kernel family is quantified before the probability space, the Brownian motion and the initial law, so it depends on $(Q,A,b)$ alone; it does not depend on $s$ (stationarity). The Markov property is stated with respect to the natural filtration of $X$, which by (a) contains that of $Z$. Brownian motion with a random initial state and the processes $Y,Z$ are the definitions of `HarrisonReimanRBM.Orthant.Process`; $X(0)$ is independent of the whole increment process. The filtration is not completed. Conditional probability is the conditional expectation of the indicator of $\{Z(s+t)\in B\}$. That processes $(Y,Z)$ as in the hypotheses exist is the existence part of Theorem 1, the referenced `Reiman84.QueueLength.lemma_1`.
-- source:
--   Harrison & Reiman, Reflected Brownian Motion on an Orthant, Ann. Probab. 9(2) (1981), p. 305, Corollary 1 (a)–(c), with the construction of Z in the preceding paragraph

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_HarrisonReimanRBM_Orthant_Basic
import Definitions.Def_HarrisonReimanRBM_Orthant_Process

namespace HarrisonReimanRBM.Orthant

open MeasureTheory ProbabilityTheory Reiman84.QueueLength

/-- Corollary 1, p. 305. Fix `K ≥ 1`, `Q` as in §1, a covariance matrix `A` (symmetric,
nonnegative definite) and a drift vector `b`. There is a family `κ = (κ_t)` of Markov kernels on
`ℝ^K`, depending only on `(Q, A, b)`, such that for every probability space `(Ω, 𝓕, P)`, every
Brownian motion `X` with covariance `A`, drift `b`, `X(0) ∈ S` a.s. and `X(0)` independent of
the increments, and `Y = ψ(X)`, `Z = φ(X)` (set to `0` off `{X ∈ C_S}`):
(a) `Y(t)` and `Z(t)` are `𝓕ₜ`-measurable for each `t ≥ 0`, `𝓕ₜ = 𝓕(X(s); 0 ≤ s ≤ t)`;
(b) `Y` and `Z` satisfy (1)–(4) almost surely, and any other pair of processes satisfying
(1)–(4) almost surely agrees with `(Y, Z)` at all `t ≥ 0`, almost surely;
(c) `Z` is a Markov process with respect to `(𝓕ₜ)` with stationary transition probabilities
`κ`: `P[Z(s + t) ∈ B | 𝓕ₛ] = κ_t(Z(s), B)` almost surely, for all `s, t ≥ 0` and Borel `B`. -/
theorem corollary_1 {K : ℕ} (hK : 0 < K) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ : IsReflectionMatrix Q) (A : Matrix (Fin K) (Fin K) ℝ) (hA : A.PosSemidef)
    (b : Fin K → ℝ) :
    ∃ κ : ℝ → Kernel (Fin K → ℝ) (Fin K → ℝ), (∀ t, IsMarkovKernel (κ t)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X Y Z : Ω → ℝ → Fin K → ℝ),
        IsBMFrom b A P X → IsRBMConstruction Q X Y Z →
        -- (a) adaptedness to the natural filtration of `X`
        (∀ t : ℝ, 0 ≤ t →
          Measurable[naturalFiltration X t] (fun ω => Y ω t) ∧
          Measurable[naturalFiltration X t] (fun ω => Z ω t)) ∧
        -- (b) (1)–(4) hold almost surely, and uniquely up to a null set
        (∀ᵐ ω ∂P, IsReflectionPair Q (X ω) (Y ω) (Z ω)) ∧
        (∀ Y' Z' : Ω → ℝ → Fin K → ℝ,
          (∀ᵐ ω ∂P, IsReflectionPair Q (X ω) (Y' ω) (Z' ω)) →
          ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Y' ω t = Y ω t ∧ Z' ω t = Z ω t) ∧
        -- (c) Markov property with stationary transition probabilities `κ`
        (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ B : Set (Fin K → ℝ), MeasurableSet B →
          P[Set.indicator {ω | Z ω (s + t) ∈ B} (fun _ => (1 : ℝ)) | naturalFiltration X s]
            =ᵐ[P] fun ω => (κ t (Z ω s) B).toReal) := by sorry

end HarrisonReimanRBM.Orthant
