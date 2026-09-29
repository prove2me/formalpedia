-- Prove2me | Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
-- name    : M4aHerbrand.unitIdele_mem_idelicNorm_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/94b2c1ac-bf67-5c95-bf23-1835bcd51e9b
-- title:
--   Congruence units at ramified places are idelic norms
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ that is Galois, let $n = [L:K]$, and let $B$ be an adele base-change datum for $(\mathcal{O}_K,K)\to(\mathcal{O}_L,L)$: a ring homomorphism $\beta\colon \mathbb{A}_K\to\mathbb{A}_L$ commuting with the structure maps from $K$, together with an $\mathbb{A}_K$-algebra isomorphism $\mathbb{A}_K\otimes_K L\simeq \mathbb{A}_L$ carrying $1\otimes f$ to the image of $f$. Let $u$ be a unit of $\mathbb{A}_K$ such that: (i) at every $v$ in the height-one spectrum of $\mathcal{O}_K$ the valuation of the $v$-component of the finite part of $u$ equals $1$; (ii) for every such $v$ at which the inertia subgroup in $\mathrm{Gal}(L/K)$ of the chosen prime [`LanglandsTunnell.P2.Artin.primeAbove K L v`](def/LanglandsTunnell_ArtinFrobenius.html#L40) of $\mathcal{O}_L$ above $v$ is nontrivial, the valuation of $u_v-1$ is at most $\exp(-N(v))$ with $N(v) = 1+\sum_{p \mid n}\bigl(\mathrm{ord}_p(n)+1\bigr)\,e\bigl(p\mathbb{Z},v\bigr)$, the sum over the prime factors of $n$; (iii) at every real infinite place $w$ of $K$ that is not unramified in $L$, the image of the $w$-component of the infinite part of $u$ under the embedding of the completion into $\mathbb{R}$ attached to $w$ being real is positive. Then $u$ lies in the range of the homomorphism on unit groups induced by the $\mathbb{A}_K$-algebra norm of $\mathbb{A}_L$, $\mathbb{A}_L$ being an $\mathbb{A}_K$-algebra via $\beta$.
--
--   This is the idelic form of the statement that local units which are sufficiently congruent to $1$ at the ramified finite places, and positive at the real places ramifying in $L$, are norms from $L$; the exponent $N(v)$ is an explicit sufficient depth in the higher unit filtration, not a sharp one. It is used in the construction of Hecke characters with prescribed local behaviour and, in the Langlands–Tunnell part of the argument, to produce ideles in the image of the idelic norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range.lean

import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_LanglandsTunnell_ArtinFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain WithZero M4aHerbrand

theorem M4aHerbrand.unitIdele_mem_idelicNorm_range
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hunit : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1)
    (hcong : ∀ v : HeightOneSpectrum (𝓞 K),
      (LanglandsTunnell.P2.Artin.primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ →
        Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1) ≤
          exp (-((1 + ∑ p ∈ (Module.finrank K L).primeFactors,
            ((Module.finrank K L).factorization p + 1) *
              Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal : ℕ) : ℤ)))
    (harch : ∀ (w : InfinitePlace K) (hw : w.IsReal), ¬ w.IsUnramifiedIn L →
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        (((u : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) w)) :
    u ∈ B.idelicNorm.range := by sorry
