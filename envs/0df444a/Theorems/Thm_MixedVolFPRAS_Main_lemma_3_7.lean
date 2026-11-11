-- Prove2me | Theorems.Thm_MixedVolFPRAS_Main_lemma_3_7
-- name    : MixedVolFPRAS.Main.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:31:43.8069+00:00
-- url     : https://prove2.me/theorems/0ee4d80a-8213-4e0b-ac05-c6eeabcb6bdb
-- title:
--   Lemma 3.7 — ψ = D_{n−1}(D²h_{K₁},…,D²h_{K_{n−1}}) > 0 and ‖∇_{Sⁿ⁻¹} log ψ‖ ≤ (n−1)M/λ ≤ nM/λ
-- statement:
--   Let $n\ge3$, fix $\Lambda\ge1\ge\lambda>0$ and $M>0$, and let $K_1,\dots,K_{n-1}\subseteq\mathbb{R}^n$ be bodies each of which is $(\lambda,\Lambda,M)$-smooth or equal to $B_2^n$. Define
--
--   $$\psi(\theta)=D_{n-1}\big(D^2h_{K_1}(\theta),\dots,D^2h_{K_{n-1}}(\theta)\big).$$
--
--   Then $\psi>0$ on $S^{n-1}$, and at every $\theta\in S^{n-1}$ the function $\log\psi$ is differentiable on the sphere with
--
--   $$\|\nabla_{S^{n-1}}\log\psi(\theta)\|_2\le\frac{(n-1)M}{\lambda}\le\frac{nM}{\lambda}.$$
--
--   The case where all bodies are smooth is the lemma's main statement; allowing any of them to be $B_2^n$ is its last sentence ("the same bound holds if any of the bodies are replaced by $B_2^n$"). This is the Lipschitz condition on $\log\psi$ that the sampler of Lemma 2.16 needs.
--
--   Differences from the source:
--   - reading: "the same bound holds if any of the bodies are replaced by $B_2^n$" → every $K_j$ is $(\lambda,\Lambda,M)$-smooth or equal to $B_2^n$, and both conclusions ($\psi>0$ and the bound) are asserted in every case; reason: the bound is on $\log\psi$, which presupposes $\psi>0$, and $D^2h_{B_2^n}=I$.
--   - encoding: the parameter conditions $\Lambda\ge1\ge\lambda>0$, $M>0$ of Definition 3.2 → explicit binders (they are also inside `IsSmoothBody`); reason: they must hold when every body is $B_2^n$.
--   - encoding: $\|\nabla_{S^{n-1}}\log\psi(\theta)\|_2\le\dots$ → existence of a spherical gradient $g$ of $\log\psi$ at $\theta$ (Definition C.1) with $\|g\|\le\dots$; reason: makes the differentiability that the bound presupposes explicit.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 14, Lemma 3.7

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_MixedDiscriminant
import Definitions.Def_MixedVolFPRAS_Main_Sphere
import Definitions.Def_MixedVolFPRAS_Main_Smoothness

namespace MixedVolFPRAS.Main

/-- **Lemma 3.7.** Let `n ≥ 3`, parameters `Λ ≥ 1 ≥ λ > 0`, `M > 0`, and `K₁, …, K_{n−1}` bodies
in `ℝⁿ`, each `(λ, Λ, M)`-smooth or equal to `B₂ⁿ`. With
`ψ(θ) = D_{n−1}(D²h_{K₁}(θ), …, D²h_{K_{n−1}}(θ))`: `ψ > 0` on `Sⁿ⁻¹`, and at every `θ ∈ Sⁿ⁻¹`
`log ψ` has a spherical gradient of norm `≤ (n − 1)M/λ ≤ nM/λ`. (All bodies smooth is the main
statement; any of them equal to `B₂ⁿ` is the last sentence of the lemma.) -/
theorem lemma_3_7 {n : ℕ} (hn : 3 ≤ n) (lam Lam M : ℝ)
    (hLam : 1 ≤ Lam) (hlam1 : lam ≤ 1) (hlam : 0 < lam) (hM : 0 < M)
    (K : Fin (n - 1) → Set (E n))
    (hK : ∀ j, IsSmoothBody lam Lam M (K j) ∨ K j = unitBall n) :
    (∀ θ ∈ unitSphere n,
        0 < mixedDiscriminant (fun j => restrictedHessian (supportFunction (K j)) θ)) ∧
      ∀ θ ∈ unitSphere n, ∃ g : E n,
        IsSphGradAt (fun x => Real.log
            (mixedDiscriminant (fun j => restrictedHessian (supportFunction (K j)) x))) θ g ∧
          ‖g‖ ≤ ((n : ℝ) - 1) * M / lam ∧ ((n : ℝ) - 1) * M / lam ≤ (n : ℝ) * M / lam := by sorry

end MixedVolFPRAS.Main
