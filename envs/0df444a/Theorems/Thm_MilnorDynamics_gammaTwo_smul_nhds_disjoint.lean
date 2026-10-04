-- Prove2me | Theorems.Thm_MilnorDynamics_gammaTwo_smul_nhds_disjoint
-- name    : MilnorDynamics.gammaTwo_smul_nhds_disjoint
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T15:51:15.670756+00:00
-- url     : https://prove2.me/theorems/69e50913-f7a0-49df-b760-7c85902fae49
-- title:
--   $\Gamma(2)$ acts properly discontinuously on $\mathbb H$, freely modulo $\pm I$
-- statement:
--   Let $\mathbb H=\{\tau\in\mathbb C:\operatorname{Im}\tau>0\}$ be the upper half-plane, on which $\mathrm{SL}_2(\mathbb Z)$ acts by Möbius transformations
--   $$
--   \begin{pmatrix} a & b\\ c & d\end{pmatrix}\cdot\tau=\frac{a\tau+b}{c\tau+d},
--   $$
--   and let
--   $$
--   \Gamma(2)=\Bigl\{\gamma\in\mathrm{SL}_2(\mathbb Z):\gamma\equiv\begin{pmatrix}1&0\\0&1\end{pmatrix}\pmod 2\Bigr\}
--   $$
--   be the principal congruence subgroup of level $2$.
--
--   For every $\tau\in\mathbb H$ there is a neighbourhood $U$ of $\tau$ in $\mathbb H$ such that, for every $\gamma\in\Gamma(2)$,
--   $$
--   \gamma(U)\cap U\neq\varnothing\quad\Longrightarrow\quad\gamma=\pm I .
--   $$
--
--   In words: $\Gamma(2)$ acts properly discontinuously on $\mathbb H$, and the induced action of $\Gamma(2)/\{\pm I\}$ is free. This is the group-theoretic half of the classical fact that the modular function $\lambda$ exhibits $\mathbb H$ as a covering space of $\mathbb C\setminus\{0,1\}=\mathbb H/\Gamma(2)$, which in turn gives Milnor's Lemma 2.5 for the triply punctured sphere $\hat{\mathbb C}\setminus\{0,1,\infty\}$.
--
--   **Formalization Note** $\mathbb H$ is Mathlib's `UpperHalfPlane`, $\Gamma(2)$ is `CongruenceSubgroup.Gamma 2`, a subgroup of `SL(2, ℤ)`, and $\gamma\cdot\tau$ is Mathlib's action of `SL(2, ℤ)` on `ℍ`. The condition $\gamma(U)\cap U\neq\varnothing$ is written as "some $\sigma\in U$ has $\gamma\cdot\sigma\in U$". The matrix $-I$ acts trivially on $\mathbb H$, which is why the conclusion is $\gamma=1$ or $\gamma=-1$.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, §2, Lemma 2.5 (The Triply Punctured Sphere), p. 17; L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, Chapter 7, §3.4 (The modular function λ(τ))

import Mathlib

open Set Topology UpperHalfPlane

namespace MilnorDynamics

theorem gammaTwo_smul_nhds_disjoint (τ : ℍ) :
    ∃ U ∈ 𝓝 τ, ∀ γ ∈ CongruenceSubgroup.Gamma 2,
      (∃ σ ∈ U, γ • σ ∈ U) → γ = 1 ∨ γ = -1 := by sorry

end MilnorDynamics
