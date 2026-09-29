-- Prove2me | Theorems.Thm_M4aHerbrand_genuineAdelicNorm_componentwise
-- name    : M4aHerbrand.genuineAdelicNorm_componentwise
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/cec95a7e-d7be-5cfd-8917-8d9e3f73939f
-- title:
--   Componentwise splitting of the genuine adelic norm
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $y$ be an element of the adele ring $\mathbb{A}_L$ of $L$, viewed as a pair consisting of an infinite adele $y.1 \in \mathbb{A}_{L,\infty}$ and a finite adele $y.2$. Equip $\mathbb{A}_L$ with the $\mathbb{A}_K$-algebra structure coming from the ring homomorphism `genuineβ K L` $\colon \mathbb{A}_K \to \mathbb{A}_L$ and form $N = \mathrm{Algebra.norm}_{\mathbb{A}_K}(y) \in \mathbb{A}_K$. The assertion is twofold. First, the infinite component $N.1$ equals the norm of $y.1$ over $\mathbb{A}_{K,\infty}$, computed for the algebra structure induced by the ring homomorphism $\mathbb{A}_{K,\infty} \to \mathbb{A}_{L,\infty}$ obtained from the base-change isomorphism $\mathbb{A}_{K,\infty} \otimes_K L \cong \mathbb{A}_{L,\infty}$ assembled from the $K_v$-isomorphisms $K_v \otimes_K L \cong \prod_{w \mid v} L_w$ of `genuineInfinitePlaceData` and precomposition with $a \mapsto a \otimes 1$. Second, for every height-one prime $v$ of $\mathcal{O}_K$, the value at $v$ of the finite component $N.2$ equals $\prod_{w} \mathrm{Algebra.norm}_{K_v}(y.2\,w)$, the product being over the finitely many height-one primes $w$ of $\mathcal{O}_L$ with $w \cap \mathcal{O}_K = v$, of the norms of the local components of the finite adele $y.2$.
--
--   This is the statement that the adelic norm for the genuine base-change algebra structure is computed place by place, the archimedean part separately and each finite part as the product of the local norms $N_{L_w/K_v}$ over the places $w$ above $v$. It is used in the converse-direction arguments of the Langlands–Tunnell material, where idelic norms of adelic base-change data have to be evaluated at individual archimedean and finite places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_genuineAdelicNorm_componentwise.lean

import Definitions.Def_M4aHerbrand_GenuineBeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open M4aHerbrand.ArchSemilocal M4aHerbrand.Bridge

theorem M4aHerbrand.genuineAdelicNorm_componentwise
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (y : AdeleRing (𝓞 L) L) :
    (letI := (genuineβ K L).toAlgebra;
      Algebra.norm (AdeleRing (𝓞 K) K) y).1
      = (letI := (genuineInfinitePlaceData (K := K) (L := L)).conorm.toAlgebra;
          Algebra.norm (InfiniteAdeleRing K) y.1)
    ∧ ∀ v : HeightOneSpectrum (𝓞 K),
      letI := Extension.fintype (𝓞 K) K L (𝓞 L) v;
      ((letI := (genuineβ K L).toAlgebra;
        Algebra.norm (AdeleRing (𝓞 K) K) y).2 : FiniteAdeleRing (𝓞 K) K) v
        = ∏ w : v.Extension (𝓞 L), Algebra.norm (v.adicCompletion K) (y.2 w.1) := by sorry
