-- Prove2me | Theorems.Thm_MatchedUCLB_lemma_4_5
-- name    : MatchedUCLB.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:45:44.763084+00:00
-- url     : https://prove2.me/theorems/f8e2797f-a29c-4632-afb4-03bbe6036f8c
-- title:
--   Lemma 4.5 — the complete objective: class bounds, center gradients, unique minimizer, prefix gaps, geometric decay of the gap
-- statement:
--   Let $q=p+\nu$ with $p\ge2$, $0<\nu\le1$. There is a constant $C_H>0$ depending only on $p,\nu$ such that the following holds. Let $m,L\ge1$, $\mu,\tau_0>0$, let $(v,u)$ be an orthonormal phase frame in $\mathbb R^d$, and let $F$ be the complete objective (4.17) with the parameters (4.15), $K=5^{(q-1)/2}/c_0$ and $\eta=\gamma/(2(1+\theta))$; write $c_j$ for its centers, $s_j$ for its slopes, $\lambda=K\mu m^{a_q}$ and $\delta_j=c_1\lambda m\tau_j^q$. Then:
--
--   1. **(a)** $F$ is $p$ times continuously differentiable, and for all $x,y$
--   $$
--   D_F(y,x)\ge c_B\mu\|y-x\|^q,\qquad \|\nabla^pF(x)-\nabla^pF(y)\|\le C_H\mu m^{a_q}\|x-y\|^\nu;
--   $$
--   2. **(b)** $\nabla F(c_j)=-s_jv_j$ for $j<L$, $\nabla F(c_L)=0$, and $c_L$ is the unique minimizer of $F$;
--   3. **(c)** for $0\le j<L$, $b\le\lfloor m/4\rfloor$ and every $x\in W_{j,b}$, $F(x)-F(c_L)\ge7\delta_j$;
--   4. **(d)** with $\chi_j=F(c_j)-F(c_{j+1})$ and $D_{m,L}=F(c_0)-F(c_L)$,
--   $$
--   \chi_j=\eta^{qj}\chi_0,\qquad D_{m,L}=\chi_0\,\frac{1-\eta^{qL}}{1-\eta^q},\qquad 0<\chi_0\le2(1+c_0)\lambda m\tau_0^q,
--   $$
--   and $D_{m,L}$ is the same for every orthonormal phase frame.
--
--   Part (c) is the hardness of the instance: any point in a short prefix of phase $j$ has gap at least $7\delta_j$, while (a) gives the prescribed class parameters with constants independent of $L$.
--
--   **Formalization Note** $D_F$ is the published Bregman divergence `AdaGradDHS.Diag.bregman`; $\chi_j$ is stated for $j<L$.
--
--   Differences from the source:
--   - encoding: ℝ^d, ∇^kF, ⟨∇F(x), v⟩ → EuclideanSpace ℝ (Fin d), iteratedFDeriv ℝ k F, fderiv ℝ F x v; reason: Lean convention; the norm of iteratedFDeriv is the operator norm of Sec. 3; same instances
--   - encoding: q = p + ν → a real binder q with the hypothesis hq : q = p + ν; reason: notation only; every instance has q = p + ν
--   - reading: (a) bounds ∇^pF → (a) also asserts ContDiff ℝ p F; reason: the printed bound presupposes that ∇^pF exists; Lemma E.10 (p.90) states F ∈ C^{p,ν}
--   - reading: C_H := C_B + 2C_AK depends only on p, ν → ∃ C_H > 0 chosen before d, m, L, μ, τ_0 and the frame; reason: C_B and C_A are themselves existential constants of Lemmas 4.3 and 4.4, so the formula fixes no particular number; the content is a constant depending only on p, ν
--   - encoding: G_j = ‖∇B(c_{j+1}) − ∇B(c_j)‖ = μR_j^{q−1} → G_j := μR_j^{q−1} (objG); reason: Definition E.1 states the two are equal; the closed formula is the one Lemma 4.4 is applied with
--   - encoding: D_{m,L} is independent of the orthonormal phase directions → every phase frame (v', u') in the same ℝ^d gives the same objGap; reason: direct transcription
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Lemma 4.5, p.10, Eqs. (4.15)–(4.18)

import Mathlib
import Definitions.Def_MatchedUCLB_objective
import Definitions.Def_MatchedUCLB_objDelta
import Definitions.Def_MatchedUCLB_objGap
import Definitions.Def_MatchedUCLB_IsPhaseFrame
import Definitions.Def_MatchedUCLB_prefixSpace
import Definitions.Def_MatchedUCLB_HolderBound
import Definitions.Def_MatchedUCLB_cB
import Definitions.Def_AdaGradDHS_Diag_bregman

open scoped ContDiff Topology

namespace MatchedUCLB

/-- **Lemma 4.5 (the complete objective).** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Lemma 4.5, p.10: "Let `m, L ≥ 1` and
`μ, τ_0 > 0`. Choose the parameters in Eq. (4.15) with `K = 5^{(q−1)/2}/c_0` and `η = γ/(2(1+θ))`, and
construct `B, A_j` by Eqs. (4.4) and (4.12). Then `F` in Eq. (4.17) satisfies: (a) For all `x, y`,
`D_F(y, x) ≥ c_Bμ‖y − x‖^q`, `‖∇^pF(x) − ∇^pF(y)‖ ≤ C_Hμm^{a_q}‖x − y‖^ν`, where `C_H := C_B + 2C_AK`
depends only on `p, ν`. (b) `∇F(c_j) = −s_jv_j` for `j < L`, `∇F(c_L) = 0`, and `c_L` is the unique
minimizer. (c) Every `x ∈ W_{j,b}` with `b ≤ ⌊m/4⌋` satisfies `F(x) − F(c_L) ≥ 7δ_j`, where
`δ_j = c_1λmτ_j^q` and `c_1 = 2^{−q−3}/q`. (d) Define … `χ_j := F(c_j) − F(c_{j+1})`. The initial
optimality gap `D_{m,L} := F(c_0) − F(c_L)` satisfies `χ_j = η^{qj}χ_0`,
`D_{m,L} = χ_0(1 − η^{qL})/(1 − η^q)` (4.18). Here `0 < χ_0 ≤ 2(1 + c_0)λmτ_0^q`. The value of `D_{m,L}`
is independent of the orthonormal phase directions."

**Formalization Note.** `q` is a separate real binder with the hypothesis `q = p + ν` (the matched order of the paper), so that every formula can be written in `q`. `F = objective q μ L τ₀ v u` (Definition E.8), `c_j = objCenter`,
`s_j = objSlope`, `δ_j = objDelta`, `λ = objLam q μ m`, `D_{m,L} = objGap`, and the orthonormal blocks
are a phase frame (`IsPhaseFrame`). `C_H` is existential and chosen before `d, m, L, μ, τ_0` and the
frame. `ContDiff ℝ p F` is stated in (a): the printed (a) bounds `∇^pF`, which presupposes it
(Lemma E.10 states `F ∈ C^{p,ν}`). "Unique minimizer" is: `c_L` minimizes `F`, and every minimizer
equals `c_L`. `χ_j` is stated for `j < L`. "Independent of the orthonormal phase directions": every
other phase frame in the same `ℝ^d` gives the same `D_{m,L}`. -/
theorem lemma_4_5 (p : ℕ) (hp : 2 ≤ p) (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (q : ℝ) (hq : q = (p : ℝ) + ν) :
    ∃ CH : ℝ, 0 < CH ∧
    ∀ (d m L : ℕ) (μ τ₀ : ℝ) (v : ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → Fin m → EuclideanSpace ℝ (Fin d)),
      1 ≤ m → 1 ≤ L → 0 < μ → 0 < τ₀ → IsPhaseFrame L v u →
      -- (a)
      (ContDiff ℝ p (objective q μ L τ₀ v u) ∧
        (∀ x y : EuclideanSpace ℝ (Fin d), cB q * μ * ‖y - x‖ ^ q ≤ AdaGradDHS.Diag.bregman (objective q μ L τ₀ v u) y x) ∧
        HolderBound p ν (CH * μ * (m : ℝ) ^ aQ q) (objective q μ L τ₀ v u)) ∧
      -- (b)
      ((∀ j : ℕ, j < L → gradient (objective q μ L τ₀ v u) (objCenter q τ₀ v u j) = -(objSlope q μ τ₀ v u j • v j)) ∧
        gradient (objective q μ L τ₀ v u) (objCenter q τ₀ v u L) = 0 ∧
        (∀ y : EuclideanSpace ℝ (Fin d), objective q μ L τ₀ v u (objCenter q τ₀ v u L) ≤ objective q μ L τ₀ v u y) ∧
        (∀ y : EuclideanSpace ℝ (Fin d), (∀ z : EuclideanSpace ℝ (Fin d), objective q μ L τ₀ v u y ≤ objective q μ L τ₀ v u z) → y = objCenter q τ₀ v u L)) ∧
      -- (c)
      (∀ j : ℕ, j < L → ∀ b : ℕ, b ≤ m / 4 → ∀ x ∈ prefixSpace v u j b,
        objective q μ L τ₀ v u (objCenter q τ₀ v u L) + 7 * objDelta q μ m τ₀ j ≤ objective q μ L τ₀ v u x) ∧
      -- (d)
      ((∀ j : ℕ, j < L → objective q μ L τ₀ v u (objCenter q τ₀ v u j) - objective q μ L τ₀ v u (objCenter q τ₀ v u (j + 1)) =
          eta q ^ (q * j) * (objective q μ L τ₀ v u (objCenter q τ₀ v u 0) - objective q μ L τ₀ v u (objCenter q τ₀ v u 1))) ∧
        objGap q μ L τ₀ v u =
          (objective q μ L τ₀ v u (objCenter q τ₀ v u 0) - objective q μ L τ₀ v u (objCenter q τ₀ v u 1)) * (1 - eta q ^ (q * L)) / (1 - eta q ^ q) ∧
        0 < objective q μ L τ₀ v u (objCenter q τ₀ v u 0) - objective q μ L τ₀ v u (objCenter q τ₀ v u 1) ∧
        objective q μ L τ₀ v u (objCenter q τ₀ v u 0) - objective q μ L τ₀ v u (objCenter q τ₀ v u 1) ≤ 2 * (1 + c0 q) * objLam q μ m * m * τ₀ ^ q ∧
        ∀ (v' : ℕ → EuclideanSpace ℝ (Fin d)) (u' : ℕ → Fin m → EuclideanSpace ℝ (Fin d)), IsPhaseFrame L v' u' →
          objGap q μ L τ₀ v' u' = objGap q μ L τ₀ v u) := by sorry

end MatchedUCLB
