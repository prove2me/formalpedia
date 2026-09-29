-- Prove2me | Theorems.Thm_IharaTower_RungDatum_exists_restrict
-- name    : IharaTower.RungDatum.exists_restrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/92e413de-d6b1-5969-b8cb-8f25e6f425ee
-- title:
--   Restricting a rung datum along an isometric embedding
-- statement:
--   Fix a commutative ring $\mathcal{O}$, three commutative $\mathcal{O}$-algebras $T_0, T_a, T_1$, and modules $M_0, M_a, M_1$ over $T_0, T_a, T_1$ respectively, each also an $\mathcal{O}$-module compatibly (scalar-tower instances). Let $P_0, P_a, P_1$ be level pairings on $M_0, M_a, M_1$: each consists of an $\mathcal{O}$-bilinear form $B$ with values in $\mathcal{O}$ that is self-adjoint for the action of the relevant Hecke algebra, $B(t\cdot m, n) = B(m, t\cdot n)$, and whose associated map $M \to (M \to_{\mathcal{O}} \mathcal{O})$ is bijective. Let $R$ be a rung datum from $(T_0, M_0, P_0)$ to $(T_a, M_a, P_a)$, i.e. an $\mathcal{O}$-algebra map $R.\mathrm{res} : T_a \to T_0$, $\mathcal{O}$-linear maps $R.i : M_0 \to M_a$ and $R.j : M_a \to M_0$, an element $R.\Delta \in T_0$, together with the adjointness $P_0.B(R.j\,m', m) = P_a.B(m', R.i\,m)$ and $R.j \circ R.i = R.\Delta \cdot \mathrm{id}$. Assume given an injective $\mathcal{O}$-linear $\iota : M_1 \to M_a$ with $P_1.B(x,y) = P_a.B(\iota x, \iota y)$ for all $x,y \in M_1$, and assume $R.i\,m$ lies in the range of $\iota$ for every $m \in M_0$. Then there exist $\mathcal{O}$-linear maps $i_\alpha : M_0 \to M_1$ and $j_\alpha : M_1 \to M_0$ such that $\iota(i_\alpha m) = R.i\,m$ for all $m$, $j_\alpha m' = R.j(\iota m')$ for all $m'$, $P_0.B(j_\alpha m', m) = P_1.B(m', i_\alpha m)$ for all $m', m$, and $j_\alpha(i_\alpha m) = R.\Delta \cdot m$ for all $m$.
--
--   This is the bookkeeping step that transports a rung of the Ihara-type ladder from a raised level to a submodule of it cut out isometrically by $\iota$ — typically the unit-root (ordinary $\alpha$-) corner inside the full level at $p$ — producing there maps $i_\alpha, j_\alpha$ with the same adjointness and the same composite $R.\Delta$. It is used in the construction of the Hecke-module rung at the residue characteristic unit root from corner data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaTower_RungDatum_exists_restrict.lean

import Mathlib
import Definitions.Def_HeckeModule_IharaRungDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IharaTower

theorem IharaTower.RungDatum.exists_restrict {𝒪 : Type} [CommRing 𝒪]
    {T₀ Tₐ T₁ : Type} [CommRing T₀] [CommRing Tₐ] [CommRing T₁] [Algebra 𝒪 T₀] [Algebra 𝒪 Tₐ] [Algebra 𝒪 T₁]
    {M₀ Mₐ M₁ : Type} [AddCommGroup M₀] [AddCommGroup Mₐ] [AddCommGroup M₁]
    [Module T₀ M₀] [Module Tₐ Mₐ] [Module T₁ M₁] [Module 𝒪 M₀] [Module 𝒪 Mₐ] [Module 𝒪 M₁]
    [IsScalarTower 𝒪 T₀ M₀] [IsScalarTower 𝒪 Tₐ Mₐ] [IsScalarTower 𝒪 T₁ M₁]
    {P₀ : LevelPairing (𝒪 := 𝒪) T₀ M₀} {Pₐ : LevelPairing (𝒪 := 𝒪) Tₐ Mₐ} (P₁ : LevelPairing (𝒪 := 𝒪) T₁ M₁)
    (R : RungDatum (𝒪 := 𝒪) T₀ Tₐ M₀ Mₐ P₀ Pₐ)
    (ι : M₁ →ₗ[𝒪] Mₐ) (hι : Function.Injective ι)
    (hB : ∀ x y : M₁, P₁.B x y = Pₐ.B (ι x) (ι y))
    (hcomb : ∀ m : M₀, R.i m ∈ LinearMap.range ι) :
    ∃ (iα : M₀ →ₗ[𝒪] M₁) (jα : M₁ →ₗ[𝒪] M₀),
      (∀ m, ι (iα m) = R.i m) ∧ (∀ m', jα m' = R.j (ι m')) ∧
      (∀ m' m, P₀.B (jα m') m = P₁.B m' (iα m)) ∧ (∀ m, jα (iα m) = R.Δ • m) := by sorry
