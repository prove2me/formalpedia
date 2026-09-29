-- Prove2me | Theorems.Thm_Module_quasiIso_baseChange_of_quasiIso_of_flat
-- name    : Module.quasiIso_baseChange_of_quasiIso_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/524d5e5b-78d2-5dcc-b10d-dfc0445a8a1c
-- title:
--   Base change preserves quasi-isomorphisms of bounded flat complexes
-- statement:
--   Let $R$ be a commutative ring. Let $K$ be a family of $R$-modules $K_i$ ($i\in\mathbb N$), each flat over $R$, equipped with $R$-linear maps $\delta_i\colon K_i\to K_{i+1}$ satisfying $\delta_{i+1}\circ\delta_i=0$, and let $C$ be a second such family of flat $R$-modules with maps $d_i\colon C_i\to C_{i+1}$ satisfying $d_{i+1}\circ d_i=0$. Let $n\in\mathbb N$ be such that $K_i$ and $C_i$ are subsingletons for all $i>n$. Let $\varphi_i\colon K_i\to C_i$ be $R$-linear maps with $d_i\circ\varphi_i=\varphi_{i+1}\circ\delta_i$ for all $i$, and assume the following four elementwise quasi-isomorphism conditions: every $x\in K_0$ with $\delta_0x=0$ and $\varphi_0x=0$ vanishes; every $y\in C_0$ with $d_0y=0$ is $\varphi_0x$ for some $x\in K_0$ with $\delta_0x=0$; for every $i$, any $x\in K_{i+1}$ with $\delta_{i+1}x=0$ whose image $\varphi_{i+1}x$ lies in the range of $d_i$ lies in the range of $\delta_i$; and for every $i$ and every $y\in C_{i+1}$ with $d_{i+1}y=0$ there is $x\in K_{i+1}$ with $\delta_{i+1}x=0$ and $\varphi_{i+1}x-y$ in the range of $d_i$. Then for every commutative $R$-algebra $A$ the same four conditions hold for the base-changed families $A\otimes_R K_i$, $A\otimes_R C_i$ with the maps $\delta_i\otimes\mathrm{id}$, $d_i\otimes\mathrm{id}$ and $\varphi_i\otimes\mathrm{id}$ obtained by `LinearMap.baseChange`.
--
--   This is the statement that a quasi-isomorphism between complexes of flat modules concentrated in degrees $0,\dots,n$ remains a quasi-isomorphism after an arbitrary base change, with the hypotheses and conclusion spelled out elementwise rather than through cohomology objects; no Noetherian or finiteness assumption occurs. It is used in the cohomological part of the project: in the construction of a projective complex computing the Čech cohomology of a locally trivial presheaf of modules after any base change, in the semicontinuity statement for Čech ranks over residue fields, and in the invariance of the alternating sum of the ranks of the cohomology of a flat complex under base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_quasiIso_baseChange_of_quasiIso_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.quasiIso_baseChange_of_quasiIso_of_flat
    (R : Type u) [CommRing R]
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] [∀ i, Module.Flat R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hKbdd : ∀ i, n < i → Subsingleton (K i)) (hCbdd : ∀ i, n < i → Subsingleton (C i))
    (φ : ∀ i, K i →ₗ[R] C i) (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
    (h0inj : ∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0)
    (h0surj : ∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y)
    (hinj : ∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) →
      x ∈ LinearMap.range (δ i))
    (hsurj : ∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
      ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i))
    (A : Type u) [CommRing A] [Algebra R A] :
    (∀ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 → (φ 0).baseChange A x = 0 → x = 0) ∧
    (∀ y : A ⊗[R] C 0, (d 0).baseChange A y = 0 →
      ∃ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 ∧ (φ 0).baseChange A x = y) ∧
    (∀ (i : ℕ) (x : A ⊗[R] K (i + 1)), (δ (i + 1)).baseChange A x = 0 →
      (φ (i + 1)).baseChange A x ∈ LinearMap.range ((d i).baseChange A) →
        x ∈ LinearMap.range ((δ i).baseChange A)) ∧
    (∀ (i : ℕ) (y : A ⊗[R] C (i + 1)), (d (i + 1)).baseChange A y = 0 →
      ∃ x : A ⊗[R] K (i + 1), (δ (i + 1)).baseChange A x = 0 ∧
        (φ (i + 1)).baseChange A x - y ∈ LinearMap.range ((d i).baseChange A)) := by sorry
