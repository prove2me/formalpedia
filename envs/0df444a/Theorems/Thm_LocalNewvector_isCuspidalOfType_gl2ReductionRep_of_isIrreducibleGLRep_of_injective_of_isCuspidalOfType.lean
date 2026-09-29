-- Prove2me | Theorems.Thm_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType
-- name    : LocalNewvector.isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/0a5af462-5b64-5235-994b-54af14ef9a43
-- title:
--   Cuspidality of type θ transfers along an equivariant injection
-- statement:
--   Let $q$ be a prime and let $V$ be a complex vector space carrying a distributive action of $\mathrm{GL}_2(\mathbb{Q}_q)$ commuting with the scalars, such that the subspace $V^{K(1)}$ of vectors fixed by every element of [`FLT.SmoothVectors.gl2CongruenceSubgroup q 1`](def/RepTheory_GL2CongruenceSubgroup.html#L181) — the group of $g\in\mathrm{GL}_2(\mathbb{Q}_q)$ all of whose entries of $g-1$ and of $g^{-1}-1$ have norm at most $q^{-1}$ — is finite dimensional over $\mathbb{C}$. Assume [`LocalNewvector.IsIrreducibleGLRep q V`](def/LocalNewvector_ConductorDatum.html#L102): $V$ contains a nonzero vector and every $\mathbb{C}$-submodule of $V$ stable under the action of $\mathrm{GL}_2(\mathbb{Q}_q)$ is $\bot$ or $\top$. Let $\theta:\mathbb{F}_{q^2}^\times\to\mathbb{C}^\times$ be a character, let $X$ be a finite-dimensional complex vector space with a representation $\rho$ of $\mathrm{GL}_2(\mathbb{Z}/q)$ which is cuspidal of type $\theta$, i.e. $\dim_{\mathbb{C}}X=q-1$, the only vector fixed by all $\rho(\text{unipotent }t)$, $t\in\mathbb{Z}/q$, is $0$, $\rho$ is trivial on the scalar matrices $c\in(\mathbb{Z}/q)^\times$, and for every $\alpha\in\mathbb{F}_{q^2}^\times$ one has $\operatorname{charpoly}(\rho(\text{torus }\alpha))\cdot (X-\theta(\alpha))(X-\theta(\alpha)^{-1})=\operatorname{charpoly}((\mathrm{ind}\ q\ \mathbb{C})(\text{torus }\alpha))$. Suppose finally that there is an injective $\mathbb{C}$-linear map $\varphi:X\to V^{K(1)}$ intertwining $\rho$ with [`LocalNewvector.gl2ReductionRep q V`](def/LocalNewvector_ReductionFunctor.html#L187), the representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on $V^{K(1)}$ obtained by descending the action of the integral congruence subgroup through reduction modulo $q$. Then [`LocalNewvector.gl2ReductionRep q V`](def/LocalNewvector_ReductionFunctor.html#L187) is itself cuspidal of type $\theta$ in the same sense.
--
--   In the local theory of newvectors this is the statement that an irreducible smooth representation of $\mathrm{GL}_2(\mathbb{Q}_q)$ whose $K(q)$-invariants contain a cuspidal type $\theta$ has invariants exhausted by that type, so that $\dim V^{K(q)}=q-1$ and the embedding is an isomorphism of $\mathrm{GL}_2(\mathbb{F}_q)$-representations. It feeds the newform-level analysis of `gl2ReductionRep`, where the full invariant subspace must be identified with a cuspidal representation of type $\theta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_ReductionFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LocalNewvector.isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType
    (q : ℕ) [Fact q.Prime]
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (hV : LocalNewvector.IsIrreducibleGLRep q V) (θ : (GaloisField q 2)ˣ →* ℂˣ)
    {X : Type*} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] {ρ : Representation ℂ (CuspidalType.GL2 q) X}
    (hρ : CuspidalType.IsCuspidalOfType θ ρ)
    (φ : X →ₗ[ℂ] ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V))
    (hφ : ∀ g x, φ (ρ g x) = LocalNewvector.gl2ReductionRep q V g (φ x)) (hφinj : Function.Injective φ) :
    CuspidalType.IsCuspidalOfType θ (LocalNewvector.gl2ReductionRep q V) := by sorry
