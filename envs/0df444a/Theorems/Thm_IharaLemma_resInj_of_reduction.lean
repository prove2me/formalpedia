-- Prove2me | Theorems.Thm_IharaLemma_resInj_of_reduction
-- name    : IharaLemma.resInj_of_reduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/915f15b9-bb9e-5ad3-a43c-3e2988b02881
-- title:
--   Divisibility reflected by an injective reduction
-- statement:
--   Let $R$ be a commutative ring and let $V$, $L$, $V_k$, $L_k$ be $R$-modules. Fix an element $\varpi \in R$ and $R$-linear maps $f : V \to L$, $\mathrm{red}_V : V \to V_k$, $\mathrm{red}_L : L \to L_k$ and $f_k : V_k \to L_k$. Assume: (i) the square commutes pointwise, $\mathrm{red}_L(f(v)) = f_k(\mathrm{red}_V(v))$ for all $v \in V$; (ii) the kernel of $\mathrm{red}_V$ is contained in $\varpi V$, i.e. every $v$ with $\mathrm{red}_V(v) = 0$ can be written $v = \varpi \cdot v_1$ for some $v_1 \in V$; (iii) $\mathrm{red}_L$ kills $\varpi L$, i.e. $\mathrm{red}_L(\varpi \cdot x) = 0$ for every $x \in L$; and (iv) $f_k$ is injective. Then for every $v \in V$ and every $x \in L$ with $f(v) = \varpi \cdot x$ there exists $v_1 \in V$ with $v = \varpi \cdot v_1$. In other words, under these hypotheses $f^{-1}(\varpi L) \subseteq \varpi V$.
--
--   This is the elementary module-theoretic step underlying arguments of Ihara type, where $V$ and $L$ are lattices, $\mathrm{red}_V$ and $\mathrm{red}_L$ are reductions modulo a uniformiser $\varpi$, and injectivity of the reduced map $f_k$ is used to deduce that $f$ does not create new $\varpi$-divisibility. It is used in the construction of the cohomological carrier ([`CohCarrier.injective_and_residual_of_isEis`](thm.html#CohCarrier.injective_and_residual_of_isEis)) and in the auxiliary-level comparison [`CuspForm.AuxLevel.exists_linearEquiv_baseML_prod_ML`](thm.html#CuspForm.AuxLevel.exists_linearEquiv_baseML_prod_ML).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_resInj_of_reduction.lean

import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaLemma.resInj_of_reduction {R : Type*} [CommRing R] {V L Vk Lk : Type*}
    [AddCommGroup V] [Module R V] [AddCommGroup L] [Module R L]
    [AddCommGroup Vk] [Module R Vk] [AddCommGroup Lk] [Module R Lk]
    (ϖ : R) (f : V →ₗ[R] L) (redV : V →ₗ[R] Vk) (redL : L →ₗ[R] Lk)
    (fk : Vk →ₗ[R] Lk) (hsq : ∀ v, redL (f v) = fk (redV v))
    (hker : ∀ v, redV v = 0 → ∃ v₁, v = ϖ • v₁) (hϖ : ∀ x : L, redL (ϖ • x) = 0)
    (hfk : Function.Injective fk) :
    ∀ (v : V) (x : L), f v = ϖ • x → ∃ v₁ : V, v = ϖ • v₁ := by sorry
