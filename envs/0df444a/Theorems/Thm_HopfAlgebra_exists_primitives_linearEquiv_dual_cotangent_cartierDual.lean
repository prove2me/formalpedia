-- Prove2me | Theorems.Thm_HopfAlgebra_exists_primitives_linearEquiv_dual_cotangent_cartierDual
-- name    : HopfAlgebra.exists_primitives_linearEquiv_dual_cotangent_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/d29c3e35-7dd3-580a-81e5-57156966565e
-- title:
--   Primitives of H versus the dual cotangent space of H^∨
-- statement:
--   Let $k$ be a field and let $H$ be a commutative ring carrying a Hopf algebra structure over $k$ whose comultiplication is cocommutative, and assume $H$ is finite as a $k$-module. Write $P(H)$ for the $k$-submodule [`primitives k H`](def/Dieudonne_ModpRealization.html#L16) of $H$, defined as the kernel of the $k$-linear map $x \mapsto \Delta(x) - x \otimes 1 - 1 \otimes x$, i.e. the primitive elements for the comultiplication. Write $H^\vee$ for [`CartierDual k H`](def/HopfAlgebra_CartierDual.html#L12), the $k$-linear dual $\operatorname{Hom}_k(H,k)$ with its ring and bialgebra structure, and let $\mathfrak n \subseteq H^\vee$ be the kernel of the counit algebra map of $H^\vee$, with cotangent module $\mathfrak n/\mathfrak n^2$ (`Ideal.Cotangent`). The assertion is that there exists a $k$-linear equivalence $e \colon P(H) \xrightarrow{\sim} \operatorname{Hom}_k(\mathfrak n/\mathfrak n^2, k)$ such that for every primitive $x \in P(H)$ and every $\varphi \in H^\vee$ lying in $\mathfrak n$, the value of $e(x)$ on the class of $\varphi$ in $\mathfrak n/\mathfrak n^2$ equals $\varphi(x)$. Thus the equivalence is the one induced by the evaluation pairing, and it is produced as an existence statement rather than as a named map.
--
--   This is the Cartier-duality identification of the primitive elements of a finite commutative cocommutative Hopf algebra $H$ with the tangent space of the dual group scheme $\operatorname{Spec} H^\vee$, i.e. $\operatorname{Hom}_{k\text{-gp}}(\operatorname{Spec} H, \mathbb G_a) \cong (\mathfrak n/\mathfrak n^2)^*$. It feeds the dimension estimates for spaces of primitives used in the Dieudonné-theoretic analysis of finite flat group schemes, being cited by [`HopfAlgebra.le_finrank_primitives_of_finrank_eq_pow_of_nsmulAlgHom_eq`](thm.html#HopfAlgebra.le_finrank_primitives_of_finrank_eq_pow_of_nsmulAlgHom_eq) and by [`MvFormalGroup.finrank_primitives_add_le_of_ker_eq_span_nthSeries_of_finrank_eq_pow`](thm.html#MvFormalGroup.finrank_primitives_add_le_of_ker_eq_span_nthSeries_of_finrank_eq_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_primitives_linearEquiv_dual_cotangent_cartierDual.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_Dieudonne_ModpRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem HopfAlgebra.exists_primitives_linearEquiv_dual_cotangent_cartierDual
    (k : Type u) [Field k] (H : Type v) [CommRing H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
    [Module.Finite k H] :
    ∃ e : ↥(primitives k H) ≃ₗ[k]
        Module.Dual k (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))).Cotangent,
      ∀ (x : ↥(primitives k H)) (φ : CartierDual k H)
        (hφ : φ ∈ RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))),
        e x ((RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))).toCotangent ⟨φ, hφ⟩) = φ (x : H) := by sorry
