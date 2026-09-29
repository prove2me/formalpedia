-- Prove2me | Theorems.Thm_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup
-- name    : MazurAdmissible.AdmissibleChain.nonempty_of_addSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/5b0aad38-5205-501b-9529-2335195b9e78
-- title:
--   Admissible chains restrict to Galois-stable subgroups
-- statement:
--   Let $M$ be an additive abelian group, $p$ a prime, and $\Phi$ an `OpenAction` on $M$, that is, a monoid homomorphism $\Phi.\varphi$ from the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` to the additive automorphisms of $M$ whose kernel is open. Let $N$ be an additive subgroup of $M$ which is stable under the action, i.e. $\Phi.\varphi(\sigma)(x) \in N$ for every $\sigma$ and every $x \in N$, and let $\Phi_N$ be an `OpenAction` on the subtype $N$ whose action agrees with that of $\Phi$ under the inclusion: $(\Phi_N.\varphi(\sigma)(x) : M) = \Phi.\varphi(\sigma)(x)$ for all $\sigma$ and all $x \in N$. Assume given an `AdmissibleChain p Φ`, namely an $n$, a family of subgroups $M_0, \dots, M_n$ of $M$ indexed by `Fin (n+1)` with $M_0 = \bot$, $M_n = \top$ and $M_i \le M_{i+1}$, together with a Boolean tag for each of the $n$ steps, such that each layer $M_{i+1}/M_i$ has cardinality exactly $p$ and, for each step $i$, either (tag true) $\Phi.\varphi(\sigma)(x) - x \in M_i$ for all $\sigma$ and all $x \in M_{i+1}$, or (tag false) $\Phi.\varphi(\sigma)(x) - a\cdot x \in M_i$ for all $\sigma$, all $x \in M_{i+1}$ and all $a \in \mathbb{N}$ arising as $\sigma\zeta = \zeta^a$ for some primitive $p$-th root of unity $\zeta \in \overline{\mathbb{Q}}$. The conclusion is that the type `AdmissibleChain p ΦN` is nonempty; no relation between the produced chain for $N$ and the given chain $c$ is asserted.
--
--   This is the subobject half of Mazur's observation that admissible $p$-groups — those with a Galois filtration whose layers are of order $p$ with trivial or mod-$p$ cyclotomic action — form a Serre subcategory, here on the Galois-module side. It is used in the construction of an open action together with an admissible chain on the Eisenstein-primary torsion of a modular curve, via [`ModularCurve.exists_openAction_admissibleChain_eisensteinPrimaryTorsionBar`](thm.html#ModularCurve.exists_openAction_admissibleChain_eisensteinPrimaryTorsionBar), and it cites the concatenation statement [`MazurAdmissible.exists_admissibleChain_filtAlpha_eq_add`](thm.html#MazurAdmissible.exists_admissibleChain_filtAlpha_eq_add) and the transport statement [`MazurAdmissible.AdmissibleChain.exists_map_addEquiv`](thm.html#MazurAdmissible.AdmissibleChain.exists_map_addEquiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup.lean

import Mathlib
import Definitions.Def_MazurAdmissible_GaloisModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MazurAdmissible

theorem MazurAdmissible.AdmissibleChain.nonempty_of_addSubgroup
    {M : Type*} [AddCommGroup M] {p : ℕ} (hp : p.Prime) (Φ : OpenAction M)
    (N : AddSubgroup M)
    (hN : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ N, Φ.φ σ x ∈ N)
    (ΦN : OpenAction ↥N)
    (hΦN : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥N), (ΦN.φ σ x : M) = Φ.φ σ x)
    (c : AdmissibleChain p Φ) :
    Nonempty (AdmissibleChain p ΦN) := by sorry
