-- Prove2me | Theorems.Thm_HopfAlgebra_isLocalRing_and_isLocalRing_cartierDual_of_pow_eq_counit_of_frobenius_congr
-- name    : HopfAlgebra.isLocalRing_and_isLocalRing_cartierDual_of_pow_eq_counit_of_frobenius_congr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/a5038bb2-9171-5684-883b-1a0d28bb63da
-- title:
--   Local-local criterion from Ft=F² and Vt=V²
-- statement:
--   Let $R$ be a commutative local ring, let $p$ be a prime with $p\cdot 1_R$ lying in the maximal ideal of $R$, and let $H$ be a commutative ring carrying the structure of a Hopf algebra over $R$ which is finite and free as an $R$-module and whose comultiplication is cocommutative. Let $t : H \to H$ be a morphism of $R$-bialgebras (an $R$-algebra map that is simultaneously a map of coalgebras), and assume three conditions: first, there is an $m \in \mathbb{N}$ such that the $m$-fold iterate of $t$ sends every $a \in H$ to the image under the structure map $R \to H$ of $\varepsilon(a)$, where $\varepsilon$ is the counit; second, for every $a \in H$ the element $t(a)^p - a^{p^2}$ is divisible by $p$ in $H$; third, for every $R$-linear form $\varphi : H \to R$, the element $(\varphi \circ t)^{p} - \varphi^{p^2}$ is divisible by $p$ in the ring $\mathrm{Hom}_R(H,R)$ equipped with the convolution product (powers and divisibility being taken there, via `WithConv`). The conclusion is that $H$ is a local ring and that [`CartierDual R H`](def/HopfAlgebra_CartierDual.html#L12), the $R$-linear dual $\mathrm{Hom}_R(H,R)$ with its convolution ring structure, is a local ring.
--
--   In the language of group schemes, $\operatorname{Spec} H$ is a finite flat commutative group scheme $G$ over the local ring $R$ of residue characteristic $p$, and the hypotheses on $t$ say that $t$ becomes the trivial endomorphism after $m$ iterations and satisfies the special-fibre identities $F\circ t = F^2$ and $V\circ t = V^2$ for the Frobenius and Verschiebung of $G$ modulo $p$; the conclusion is that both $G$ and its Cartier dual are connected, i.e. $G$ is local-local. It is used in the construction of a finite flat local-local model for the $p$-torsion with nilpotent Hecke action on a modular curve, via [`ModularCurve.exists_finiteFlat_local_local_model_jZero_torsion_heckeNilpotent`](thm.html#ModularCurve.exists_finiteFlat_local_local_model_jZero_torsion_heckeNilpotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isLocalRing_and_isLocalRing_cartierDual_of_pow_eq_counit_of_frobenius_congr.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.isLocalRing_and_isLocalRing_cartierDual_of_pow_eq_counit_of_frobenius_congr
    {R : Type*} [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (H : Type*) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    [Coalgebra.IsCocomm R H]
    (t : H →ₐc[R] H)
    (ht : ∃ m : ℕ, ∀ a : H, (t ^ m) a = algebraMap R H (Coalgebra.counit a))
    (hF : ∀ a : H, (p : H) ∣ t a ^ p - a ^ (p ^ 2))
    (hV : ∀ φ : H →ₗ[R] R, (p : WithConv (H →ₗ[R] R)) ∣
        WithConv.toConv (φ ∘ₗ (t : H →ₗ[R] H)) ^ p - WithConv.toConv φ ^ (p ^ 2)) :
    IsLocalRing H ∧ IsLocalRing (CartierDual R H) := by sorry
