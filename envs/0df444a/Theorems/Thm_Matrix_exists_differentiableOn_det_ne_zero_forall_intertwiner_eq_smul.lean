-- Prove2me | Theorems.Thm_Matrix_exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul
-- name    : Matrix.exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/6e010dd8-f679-5195-9f38-3fa513e6379d
-- title:
--   Holomorphic intertwiner line for a holomorphic family
-- statement:
--   Let $X$ be a type, $n$ a natural number, and $\iota' : X \to M_n(\mathbb{C})$ a family of complex $n \times n$ matrices whose $\mathbb{C}$-linear span (the span of the range of $\iota'$) is all of $M_n(\mathbb{C})$. Fix $z_0 \in \mathbb{C}$, a real $\varepsilon > 0$, and a family $\rho : \mathbb{C} \to X \to M_n(\mathbb{C})$ such that for each $x \in X$ and each pair of indices $i, j$ the scalar function $z \mapsto \rho_z(x)_{ij}$ is complex differentiable on the open ball $B(z_0, \varepsilon)$. Assume further that for every $z \in B(z_0, \varepsilon)$ there exists $M \in M_n(\mathbb{C})$ with $\det M \neq 0$ and $M\,\iota'(x) = \rho_z(x)\,M$ for all $x \in X$. The conclusion asserts the existence of a real $\varepsilon'$ with $0 < \varepsilon' \le \varepsilon$ and a map $N : \mathbb{C} \to M_n(\mathbb{C})$ whose entries $z \mapsto N(z)_{ij}$ are all complex differentiable on $B(z_0, \varepsilon')$, such that for every $z \in B(z_0, \varepsilon')$: $\det N(z) \neq 0$; $N(z)\,\iota'(x) = \rho_z(x)\,N(z)$ for all $x \in X$; and every $M \in M_n(\mathbb{C})$ satisfying $M\,\iota'(x) = \rho_z(x)\,M$ for all $x \in X$ is of the form $c \cdot N(z)$ for some $c \in \mathbb{C}$.
--
--   The statement combines Schur's lemma for the full matrix algebra $M_n(\mathbb{C})$ — the intertwiners between $\iota'$ and a family conjugate to it form a single line — with a holomorphic choice of a spanning vector of that line on a possibly smaller disc. It is used in the Cerednik–Drinfeld part of the development, in the construction of a holomorphic family of uniformisations of fake elliptic curves near a point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Topology

theorem Matrix.exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul
    {X : Type} {n : ℕ} (ι' : X → Matrix (Fin n) (Fin n) ℂ)
    (hspan : Submodule.span ℂ (Set.range ι') = ⊤)
    (z₀ : ℂ) {ε : ℝ} (hε : 0 < ε) (ρ : ℂ → X → Matrix (Fin n) (Fin n) ℂ)
    (hρ : ∀ (x : X) (i j : Fin n), DifferentiableOn ℂ (fun z : ℂ => ρ z x i j) (Metric.ball z₀ ε))
    (hM : ∀ z ∈ Metric.ball z₀ ε, ∃ M : Matrix (Fin n) (Fin n) ℂ, M.det ≠ 0 ∧ ∀ x : X, M * ι' x = ρ z x * M) :
    ∃ (ε' : ℝ) (N : ℂ → Matrix (Fin n) (Fin n) ℂ), 0 < ε' ∧ ε' ≤ ε ∧
      (∀ i j : Fin n, DifferentiableOn ℂ (fun z : ℂ => N z i j) (Metric.ball z₀ ε')) ∧
      ∀ z ∈ Metric.ball z₀ ε',
        (N z).det ≠ 0 ∧ (∀ x : X, N z * ι' x = ρ z x * N z) ∧
        ∀ M : Matrix (Fin n) (Fin n) ℂ, (∀ x : X, M * ι' x = ρ z x * M) → ∃ c : ℂ, M = c • N z := by sorry
