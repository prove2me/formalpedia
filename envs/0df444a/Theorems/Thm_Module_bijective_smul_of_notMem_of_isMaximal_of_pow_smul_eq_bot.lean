-- Prove2me | Theorems.Thm_Module_bijective_smul_of_notMem_of_isMaximal_of_pow_smul_eq_bot
-- name    : Module.bijective_smul_of_notMem_of_isMaximal_of_pow_smul_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/b92fcadd-48aa-5ea3-b3f5-348d64979d48
-- title:
--   Elements outside a maximal ideal act bijectively on modules killed by a power of it
-- statement:
--   Let $T$ be a commutative ring and $M$ a $T$-module (an additive commutative group with a $T$-module structure). Let $\mathfrak{P}$ be an ideal of $T$ which is maximal, and let $k$ be a natural number. The annihilation hypothesis is stated elementwise: every $a \in \mathfrak{P}^k$ satisfies $a \cdot x = 0$ for all $x \in M$ (so $\mathfrak{P}^k$ kills $M$; the name of the declaration refers to the equivalent formulation $\mathfrak{P}^k M = 0$). Finally, let $u \in T$ with $u \notin \mathfrak{P}$. The conclusion is that the map $M \to M$, $x \mapsto u \cdot x$, given by multiplication by $u$ on $M$, is bijective (injective and surjective as a function; the statement is about the underlying map, not packaged as an isomorphism of modules).
--
--   This is the standard fact that a module annihilated by a power of a maximal ideal $\mathfrak{P}$ is a module over the local ring $T/\mathfrak{P}^k$, on which every element of $T \setminus \mathfrak{P}$ acts invertibly; equivalently such a module is its own localisation at $\mathfrak{P}$. It is used in the construction of a retraction onto the kernel of multiplication by an integer on a sheaf of points, in the analysis of the component group attached to the Eisenstein ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_bijective_smul_of_notMem_of_isMaximal_of_pow_smul_eq_bot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Module.bijective_smul_of_notMem_of_isMaximal_of_pow_smul_eq_bot
    {T : Type*} [CommRing T] {M : Type*} [AddCommGroup M] [Module T M]
    (𝔓 : Ideal T) (h𝔓 : 𝔓.IsMaximal) (k : ℕ) (hk : ∀ (a : T), a ∈ 𝔓 ^ k → ∀ x : M, a • x = 0)
    (u : T) (hu : u ∉ 𝔓) : Function.Bijective (fun x : M => u • x) := by sorry
