-- Prove2me | Theorems.Thm_NumberField_exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic
-- name    : NumberField.exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/3496a60a-0f3a-5027-a680-0c2e6e9bfaec
-- title:
--   Hasse norm theorem for cyclic extensions
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite Galois extension of $K$ whose Galois group $L \simeq_{\mathrm{alg}[K]} L$ is cyclic, and let $a$ be a unit of $K$ (that is, a nonzero element of $K$, presented as an element of $K^\times$). The hypothesis concerns the base-change datum [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87): this is a structure consisting of a ring homomorphism $\beta$ from the adele ring $\mathbb{A}_K$ of $\mathcal{O}_K \subset K$ to the adele ring $\mathbb{A}_L$ of $\mathcal{O}_L \subset L$ which is compatible with the structure maps, in the sense that $\beta$ applied to the principal adele of $x \in K$ is the principal adele of the image of $x$ in $L$, together with an $\mathbb{A}_K$-algebra equivalence $\mathbb{A}_K \otimes_K L \simeq \mathbb{A}_L$ (the $\mathbb{A}_K$-algebra structure on $\mathbb{A}_L$ being the one induced by $\beta$) carrying $1 \otimes l$ to the principal adele of $l$. Its `adelicNorm` is the algebra norm $\mathbb{A}_L \to \mathbb{A}_K$ for this algebra structure, viewed as a map of multiplicative monoids, and its `idelicNorm` is the induced homomorphism $\mathbb{A}_L^\times \to \mathbb{A}_K^\times$ on unit groups. The hypothesis is that the image of $a$ under the induced map $K^\times \to \mathbb{A}_K^\times$ lies in the range of this idelic norm. The conclusion is that there exists $b \in L$ with $\mathrm{N}_{L/K}(b) = a$, the algebra norm of $L$ over $K$ evaluated at $b$ being equal to $a$ as an element of $K$; note that $b$ is produced as an element of $L$, not as a unit, although $b \neq 0$ follows since $a \neq 0$.
--
--   This is Hasse's norm theorem in the cyclic case: an element of $K^\times$ that is everywhere locally a norm from $L$ is a global norm, equivalently the vanishing of $\hat{H}^{-1}(\mathrm{Gal}(L/K), C_L)$ for the idele class group. It is used as the arithmetic input to the local–global principle for norms attached to elliptic conjugacy classes in the automorphic-forms part of the development, where results on norm classes and on centralizer sums cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic.lean

import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (a : Kˣ)
    (ha : Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a ∈
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range) :
    ∃ b : L, Algebra.norm K b = (a : K) := by sorry
