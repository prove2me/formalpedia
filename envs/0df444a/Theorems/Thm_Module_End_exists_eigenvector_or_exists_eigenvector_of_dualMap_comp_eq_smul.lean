-- Prove2me | Theorems.Thm_Module_End_exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul
-- name    : Module.End.exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/41a2d84e-0901-51db-87ab-6c83fa8a2622
-- title:
--   Dichotomy for joint eigenvectors along an exact window
-- statement:
--   Let $K$ be a field and let $L$, $S$, $\Omega'$ be $K$-vector spaces, with $L$ and $\Omega'$ finite-dimensional; let $\iota$ be an index type. Given families of $K$-linear endomorphisms $T^L_i$ of $L$ and $T^\Omega_i$ of $\Omega'$, each family pairwise commuting, and an arbitrary family $T^S_i$ of endomorphisms of $S$; a $K$-linear map $\mathrm{res}\colon L \to S$ with $\mathrm{res}\circ T^L_i = T^S_i\circ\mathrm{res}$ for all $i$; a $K$-linear map $\Theta\colon S \to \operatorname{Hom}_K(\Omega',K)$ such that for every $v \in S$ one has $\Theta v = 0$ if and only if $v$ lies in the range of $\mathrm{res}$; scalars $c_i \in K$, all non-zero, with $\Theta(T^S_i v) = c_i\,(T^\Omega_i)^{t}(\Theta v)$ for all $i$ and all $v \in S$, where $(T^\Omega_i)^{t}$ is the dual (transpose) map; and scalars $\lambda_i \in K$ together with a non-zero $v \in S$ satisfying $T^S_i v = \lambda_i v$ for all $i$. Then at least one of the following holds: there is a non-zero $G \in L$ with $T^L_i G = \lambda_i G$ for all $i$; or there is a non-zero $\omega \in \Omega'$ with $T^\Omega_i \omega = (c_i^{-1}\lambda_i)\,\omega$ for all $i$.
--
--   This is the linear-algebra core of the window argument of Edixhoven's Proposition 7.3: a joint eigenvector of the Hecke-type operators on the middle space $S$ either lifts to a joint eigenvector on $L$ (the space mapping in) or produces, after twisting the eigenvalues by $c_i^{-1}$, a joint eigenvector on the space $\Omega'$ whose dual receives $S$. It is used by [`ModularCurve.SSHeckeV2.ssHeckeFun_window`](thm.html#ModularCurve.SSHeckeV2.ssHeckeFun_window).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.End.exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul
    {K : Type*} [Field K]
    {L S Ω' : Type*} [AddCommGroup L] [Module K L] [AddCommGroup S] [Module K S] [AddCommGroup Ω'] [Module K Ω']
    [FiniteDimensional K L] [FiniteDimensional K Ω']
    {ι : Type*}
    (TL : ι → Module.End K L) (hTL : ∀ i j, Commute (TL i) (TL j))
    (TS : ι → Module.End K S)
    (TΩ : ι → Module.End K Ω') (hTΩ : ∀ i j, Commute (TΩ i) (TΩ j))
    (res : L →ₗ[K] S) (hres : ∀ i, res ∘ₗ TL i = TS i ∘ₗ res)
    (Θ : S →ₗ[K] Module.Dual K Ω') (hexact : ∀ v : S, Θ v = 0 ↔ v ∈ LinearMap.range res)
    (c : ι → K) (hc : ∀ i, c i ≠ 0)
    (hΘ : ∀ (i : ι) (v : S), Θ (TS i v) = c i • (TΩ i).dualMap (Θ v))
    (lam : ι → K) (v : S) (hv0 : v ≠ 0) (hv : ∀ i, TS i v = lam i • v) :
    (∃ G : L, G ≠ 0 ∧ ∀ i, TL i G = lam i • G) ∨
    (∃ ω : Ω', ω ≠ 0 ∧ ∀ i, TΩ i ω = ((c i)⁻¹ * lam i) • ω) := by sorry
