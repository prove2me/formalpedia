-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
-- name    : NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/3d80a71d-4645-5ba1-ae35-226f9e89d4e5
-- title:
--   Absolute value of a continuous idele class character is a power of the idelic norm
-- statement:
--   Let $K$ be a number field, and let $\mu \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be a group homomorphism on the units of the adele ring of $K$ (formed over the ring of integers $\mathcal{O}_K$). Assume that $\mu$ is an idele class character in the sense of the predicate [`AutomorphicForm.IsIdeleClassChar`](def/AutomorphicForm_AdelicLsXi.html#L21), i.e. $\mu$ kills the principal ideles: for every $u \in K^\times$ one has $\mu(u) = 1$, where $u$ is sent into the ideles through the units map induced by the structure map $K \to \mathbb{A}_K$. Assume further that $\mu$ is continuous. The conclusion is the existence of a real number $\sigma$ such that for every idele $x$ the complex absolute value $\lVert \mu(x) \rVert$ equals $\lVert x \rVert^{\sigma}$, the real power (`rpow`) of the idelic norm $\lVert x \rVert$ of $x$, which is defined here as the real number underlying the value at $x$ of the distributive Haar character of the adele ring of $K$, that is, the module of the scaling action of $x$ on additive Haar measure on $\mathbb{A}_K$. No uniqueness of $\sigma$, and no unitarity statement about $\mu \lVert \cdot \rVert^{-\sigma}$, is asserted.
--
--   This is the classical description, in the style of Tate's thesis, of the absolute value of a quasi-character of the idele class group of a number field as a real power of the idelic module; the exponent $\sigma$ plays the role of $\operatorname{Re} s$ in the usual normalisation of Hecke characters. The proof uses the compactness of the norm-one idele class group ([`NumberField.TateGlobal.compactSpace_normOneIdeleClass`](thm.html#NumberField.TateGlobal.compactSpace_normOneIdeleClass)) together with the evaluation of the distributive Haar character at ideles trivial at the finite places as a product of archimedean norms; downstream it is invoked in the analysis of adelic zeta integrals and in the spectral and Rankin–Selberg parts of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow
    (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K μ) (hc : Continuous μ) :
    ∃ σ : ℝ, ∀ x : (AdeleRing (𝓞 K) K)ˣ, ‖((μ x : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K x ^ σ := by sorry
