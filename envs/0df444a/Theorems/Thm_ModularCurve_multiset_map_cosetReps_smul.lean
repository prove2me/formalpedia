-- Prove2me | Theorems.Thm_ModularCurve_multiset_map_cosetReps_smul
-- name    : ModularCurve.multiset_map_cosetReps_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/f6c9136a-842b-5e61-a3e7-7ca9ef748653
-- title:
--   SL₂(ℤ)-invariance of the multiset over Γ₀(ℓ)-coset representatives
-- statement:
--   Let $\ell$ be a prime, let $\alpha$ be any type, and let $F \colon \mathfrak H \to \alpha$ be a function on the upper half-plane which is invariant under $\Gamma_0(\ell)$, in the sense that $F(\gamma_0 \cdot \tau) = F(\tau)$ for every $\gamma_0 \in \Gamma_0(\ell) \subseteq \mathrm{SL}_2(\mathbb Z)$ and every $\tau \in \mathfrak H$. Consider the family of $\ell+1$ elements of $\mathrm{SL}_2(\mathbb Z)$ indexed by `Fin (ℓ + 1)` defined by case distinction on the index: the value at $0$ is the identity matrix, and the value at the successor of $b \in$ `Fin ℓ` is $S T^{b}$, where $S$ and $T$ are `ModularGroup.S` and `ModularGroup.T`. Then for every $\gamma \in \mathrm{SL}_2(\mathbb Z)$ and every $\tau \in \mathfrak H$, the multiset obtained by applying $F$ to the points $r_i \cdot (\gamma \cdot \tau)$, as $i$ runs over all of `Fin (ℓ + 1)` (the multiset underlying the universal finite set, mapped by the indicated function), equals the multiset of the values $F(r_i \cdot \tau)$ over the same index set. No assumption is made on $\alpha$ beyond its being a type; in particular the equality is an equality of multisets, not of indexed families.
--
--   The elements $1, ST^b$ ($0 \le b < \ell$) are representatives of the right cosets of $\Gamma_0(\ell)$ in $\mathrm{SL}_2(\mathbb Z)$, and the result expresses that the unordered collection of conjugated values of a $\Gamma_0(\ell)$-invariant function is unchanged by the action of the full modular group; consequently any symmetric function of the $F \circ r_i$ is $\mathrm{SL}_2(\mathbb Z)$-invariant, which is how level-$\ell$ data are made to descend to level one. It is used in the descent step [`ModularCurve.PhiGen.mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit`](thm.html#ModularCurve.PhiGen.mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_multiset_map_cosetReps_smul.lean

import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.multiset_map_cosetReps_smul (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (α : Type*) (F : UpperHalfPlane → α) (hF : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) : (Finset.univ.val.map fun i : Fin (ℓ + 1) => F ((Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i : Matrix.SpecialLinearGroup (Fin 2) ℤ) • γ • τ)) = Finset.univ.val.map fun i : Fin (ℓ + 1) => F ((Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) := by sorry
