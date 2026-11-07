-- Prove2me | Theorems.Thm_NonadaptiveSFT_lemma_10
-- name    : NonadaptiveSFT.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:21:59.552188+00:00
-- url     : https://prove2.me/theorems/c5dd2ede-f59d-4a04-82fe-5ee618a49a81
-- title:
--   Lemma 10 — the multiscale decision test: $15A_0C_0\kappa'(1+\log\kappa')$ sample pairs separate $F\ge T$ from $W\le\theta T^2$ with error $<2^{-20}$
-- statement:
--   Let $U$ and $Z$ be finite sets with probability distributions $D_U$, $D_Z$, let $V:U\times Z\to\mathbb C$, let $U\sim D_U$ and $Z\sim D_Z$ be independent, and suppose $\mathbb E|V(U,Z)|^2\le\kappa T^2$ with $T>0$ and $\kappa\ge1$. Put
--
--   $$h(u)=\mathbb E[V(u,Z)],\qquad F=\mathbb E|h(U)|,\qquad W=\mathbb E|h(U)|^2,$$
--
--   $\delta_{test}=2^{-20}$, $A_0=128$, $C_0=2^{30}$, $\theta=2^{-28}$ and $\kappa'=2^{\lceil\log\kappa\rceil}$. There is a test returning positive or negative, using exactly $15A_0C_0\kappa'(1+\log\kappa')$ pairs of samples $(u,z)$ with $u\sim D_U$ and $z\sim D_Z$, such that
--
--   $$F\ge T\ \Rightarrow\ \Pr\{\text{negative}\}<\delta_{test},\qquad W\le\theta T^2\ \Rightarrow\ \Pr\{\text{positive}\}<\delta_{test}.$$
--
--   In the locator, $U$ is a uniform point of $G$, $Z$ a uniform point of $K_j$ and $V$ the character-weighted residual, so each pair costs one point query.
--
--   **Formalization Note** The test is fixed after $T$ and $\kappa$ and before $U,Z,D_U,D_Z,V$: a number of anchors, an assignment of the pairs to anchors, and a decision rule applied to the sampled values $V(u,z)$. The anchors are independent draws from $D_U$ and the $z$'s independent draws from $D_Z$.
--
--   Differences from the source:
--   - encoding: there is a test A using exactly P pairs (u, z) with u ∼ D_U, z ∼ D_Z → ∃ n_U, an assignment π : Fin P → Fin n_U of pairs to i.i.d. D_U anchors, and a rule g on the P values V(u_{π(i)}, z_i) with i.i.d. D_Z draws z_i, chosen before U, Z, D_U, D_Z, V; reason: the paper's test is a fixed sampling procedure with anchors shared by blocks of pairs; a test chosen after V would be trivial
--   - encoding: probability distributions on finite sets → nonnegative weight functions of total mass 1; expectations and probabilities as finite weighted sums; reason: same instances
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Lemma 10, p.23 (PDF p.25)

import Mathlib

namespace NonadaptiveSFT

/-- **Lemma 10** (Decision test), p.23 (PDF p.25).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…).

Let `U`, `Z` be finite sets with distributions `D_U`, `D_Z`, `V : U × Z → ℂ`, `U ∼ D_U`, `Z ∼ D_Z`
independent, `E|V(U,Z)|² ≤ κT²` with `T > 0`, `κ ≥ 1`; `h(u) = E[V(u,Z)]`, `F = E|h(U)|`,
`W = E|h(U)|²`; `δ_test = 2^{−20}`, `A₀ = 128`, `C₀ = 2^{30}`, `θ = 2^{−28}`, `κ′ = 2^{⌈log κ⌉}`. There
is a test `A` returning positive or negative, using exactly `15A₀C₀κ′(1 + log κ′)` pairs of samples
`(u, z)` with `u ∼ D_U` and `z ∼ D_Z`, such that `F ≥ T ⇒ Pr{A outputs negative} < δ_test` and
`W ≤ θT² ⇒ Pr{A outputs positive} < δ_test`.

**Formalization Note.** A test is a **fixed decision rule on the sampled values**, chosen after `T`
and `κ` but before `U`, `Z`, `D_U`, `D_Z` and `V`: a number `n_U` of anchors, an assignment
`π : Fin P → Fin n_U` of the `P = 15A₀C₀κ′(1 + log κ′)` pairs to anchors, and a rule
`g : (Fin P → ℂ) → Bool` (`true` = positive) applied to `(V(u_{π(i)}, z_i))_{i<P}`, where the anchors
`u_1, …, u_{n_U}` are i.i.d. `D_U` and the `z_i` are i.i.d. `D_Z`, independent of the anchors. Every pair
`(u_{π(i)}, z_i)` is then a pair "with u ∼ D_U and z ∼ D_Z", and the pairs sharing an anchor are the
paper's blocks. (An existential test chosen after `V` would be trivial.) Distributions are functions
`pU : U → ℝ`, `pZ : Z → ℝ`, nonnegative with total mass `1`; expectations and probabilities are finite
weighted sums. `log κ′ = ⌈log₂ κ⌉`. -/
theorem lemma_10 :
    ∀ T κ : ℝ, 0 < T → 1 ≤ κ →
      let e : ℕ := ⌈Real.logb 2 κ⌉₊
      let P : ℕ := 15 * 128 * 2 ^ 30 * 2 ^ e * (1 + e)
      ∃ (nU : ℕ) (π : Fin P → Fin nU) (g : (Fin P → ℂ) → Bool),
        ∀ (U Z : Type) [Fintype U] [Fintype Z] (pU : U → ℝ) (pZ : Z → ℝ),
          (∀ u, 0 ≤ pU u) → ∑ u, pU u = 1 → (∀ z, 0 ≤ pZ z) → ∑ z, pZ z = 1 →
          ∀ V : U → Z → ℂ, ∑ u, ∑ z, pU u * pZ z * ‖V u z‖ ^ 2 ≤ κ * T ^ 2 →
            let h : U → ℂ := fun u => ∑ z, (pZ z : ℂ) * V u z
            let F : ℝ := ∑ u, pU u * ‖h u‖
            let W : ℝ := ∑ u, pU u * ‖h u‖ ^ 2
            let prob : Bool → ℝ := fun answer =>
              ∑ us : Fin nU → U, ∑ zs : Fin P → Z,
                (∏ i, pU (us i)) * (∏ i, pZ (zs i)) *
                  (if g (fun i => V (us (π i)) (zs i)) = answer then 1 else 0)
            (T ≤ F → prob false < (2 : ℝ) ^ (-20 : ℤ)) ∧
            (W ≤ (2 : ℝ) ^ (-28 : ℤ) * T ^ 2 → prob true < (2 : ℝ) ^ (-20 : ℤ)) := by sorry

end NonadaptiveSFT
