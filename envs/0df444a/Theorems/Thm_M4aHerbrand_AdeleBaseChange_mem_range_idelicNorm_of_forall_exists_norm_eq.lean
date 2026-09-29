-- Prove2me | Theorems.Thm_M4aHerbrand_AdeleBaseChange_mem_range_idelicNorm_of_forall_exists_norm_eq
-- name    : M4aHerbrand.AdeleBaseChange.mem_range_idelicNorm_of_forall_exists_norm_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/b8f6d4a7-7643-5680-8bf4-da0a0baadf95
-- title:
--   Local criterion for membership in the idelic norm group
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $B$ be an adèle base-change datum for the pair, that is, a ring homomorphism $\beta \colon \mathbb{A}_K \to \mathbb{A}_L$ between the adèle rings of $K$ and $L$ which is compatible with the structure maps from $K$ and from $L$, together with an $\mathbb{A}_K$-algebra isomorphism $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$ (for the $\mathbb{A}_K$-algebra structure on $\mathbb{A}_L$ given by $\beta$) sending $1 \otimes f$ to the image of $f$. Let $u$ be a unit of $\mathbb{A}_K$. Assume: (i) for every height-one prime $v$ of $\mathcal{O}_K$ there exist a height-one prime $w$ of $\mathcal{O}_L$ lying under $v$ and an element $y$ of the adic completion $L_w$ whose norm $\mathrm{N}_{L_w/K_v}(y)$, taken relative to $K_v =$ the $v$-adic completion of $K$, equals the $v$-component of the finite-adèle part of $u$; (ii) for every real infinite place $v$ of $K$ all of whose extensions to $L$ are complex, the image of the $v$-component of the infinite-adèle part of $u$ under the real embedding of the completion at $v$ is strictly positive. Then $u$ lies in the range of the induced map on unit groups of $x \mapsto \mathrm{N}_{\mathbb{A}_L/\mathbb{A}_K}(x) =$ `Algebra.norm` over $\mathbb{A}_K$, i.e. $u$ is the idelic norm of a unit of $\mathbb{A}_L$.
--
--   This is the local-to-global criterion for being an idelic norm — the easy direction of the Hasse norm principle at the level of idèles — membership in the image of the idelic norm being decided place by place, and no Galois hypothesis on $L/K$ is imposed. It is used to produce idèles in the norm group, in particular by [`M4aHerbrand.AdeleBaseChange.ideleBox_le_range_idelicNorm`](thm.html#M4aHerbrand.AdeleBaseChange.ideleBox_le_range_idelicNorm) and by the lemmas on the idelic Artin map such as [`M4aHerbrand.idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq`](thm.html#M4aHerbrand.idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq) and [`M4aHerbrand.prod_idelicArtinMap_single_eq_one`](thm.html#M4aHerbrand.prod_idelicArtinMap_single_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_AdeleBaseChange_mem_range_idelicNorm_of_forall_exists_norm_eq.lean

import Mathlib
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem M4aHerbrand.AdeleBaseChange.mem_range_idelicNorm_of_forall_exists_norm_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (B : M4aHerbrand.AdeleBaseChange (NumberField.RingOfIntegers K) K (NumberField.RingOfIntegers L) L)
    (u : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ)
    (hfin : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∃ (w : v.Extension (NumberField.RingOfIntegers L)) (y : w.1.adicCompletion L),
        Algebra.norm (v.adicCompletion K) y
          = ((u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 :
              IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K) v)
    (harch : ∀ (v : NumberField.InfinitePlace K) (hv : v.IsReal),
      (∀ w : NumberField.InfinitePlace L, w.comap (algebraMap K L) = v → w.IsComplex) →
        0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
          (((u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).1 :
              NumberField.InfiniteAdeleRing K) v)) :
    u ∈ B.idelicNorm.range := by sorry
