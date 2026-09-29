-- Prove2me | Theorems.Thm_Module_ker_baseChange_field_of_subsingleton_H1
-- name    : Module.ker_baseChange_field_of_subsingleton_H1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/5da09ff9-8dd7-57dd-bd7e-7a454f5f2798
-- title:
--   Degree-zero cohomology and base change when H¹ vanishes
-- statement:
--   Let $R$ be a commutative Noetherian ring and let $C : \mathbb{N} \to \mathrm{Type}$ be a family of $R$-modules, each flat over $R$, equipped with $R$-linear maps $d_i : C_i \to C_{i+1}$ satisfying $d_{i+1} \circ d_i = 0$ for all $i$, so that $C$ is a cochain complex indexed by $\mathbb{N}$. Assume the complex is bounded in the sense that there is an $n$ with $C_i$ a subsingleton for every $i > n$, that $\ker d_0$ is a finite $R$-module, and that for every $i$ the quotient of $\ker d_{i+1}$ by the submodule of those of its elements lying in the image of $d_i$ — that is, the cohomology $H^{i+1}(C)$ — is a finite $R$-module. Let $K$ be a field with an $R$-algebra structure, and suppose that $\ker\bigl(d_1 \otimes_R K\bigr) \le \operatorname{im}\bigl(d_0 \otimes_R K\bigr)$, i.e. the base-changed complex $K \otimes_R C$ has vanishing cohomology in degree $1$. The conclusion is twofold: the $K$-linear map $K \otimes_R \ker d_0 \to K \otimes_R C_0$ obtained by base change from the inclusion $\ker d_0 \hookrightarrow C_0$ has image exactly $\ker(d_0 \otimes_R K)$, and it is injective. Thus the canonical map $K \otimes_R H^0(C) \to H^0(K \otimes_R C)$ is bijective.
--
--   This is the degree-zero case of cohomology and base change at a field-valued point of $\operatorname{Spec} R$, in the form in which vanishing of $H^1$ after base change forces $H^0$ to commute with that base change (EGA III 7.7.5; Mumford's Abelian Varieties §5; Hartshorne III.12.11). It is formulated for $\mathbb{N}$-indexed bounded flat complexes so as to apply to alternating Čech complexes, and it is used in the comparison of pullbacks of sections of modules on schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_ker_baseChange_field_of_subsingleton_H1.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open TensorProduct

theorem Module.ker_baseChange_field_of_subsingleton_H1
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (K : Type u) [Field K] [Algebra R K]
    (hH1 : LinearMap.ker ((d 1).baseChange K) ≤ LinearMap.range ((d 0).baseChange K)) :
    LinearMap.range ((LinearMap.ker (d 0)).subtype.baseChange K) = LinearMap.ker ((d 0).baseChange K) ∧
      Function.Injective ((LinearMap.ker (d 0)).subtype.baseChange K) := by sorry
