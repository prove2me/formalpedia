-- Prove2me | Theorems.Thm_M4aHerbrand_idelicNorm_levelCongr_and_realPos
-- name    : M4aHerbrand.idelicNorm_levelCongr_and_realPos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/c27a7872-cf41-53ea-a1ee-6af06604fe9a
-- title:
--   Level congruence and real positivity descend along the idelic norm
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $B$ be an adele base-change datum for this situation: a ring homomorphism $\beta \colon \mathbb{A}_K \to \mathbb{A}_L$ compatible with the diagonal embeddings of $K$ and $L$, together with an $\mathbb{A}_K$-algebra isomorphism $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$ (the structure map being $\beta$) carrying $1 \otimes f$ to the diagonal image of $f$. Its idelic norm `B.idelicNorm` is the map on unit groups induced by the algebra norm $\mathbb{A}_L \to \mathbb{A}_K$ for this $\mathbb{A}_K$-algebra structure. Let $\mathfrak{f}$ be an ideal of $\mathcal{O}_K$, let $u$ be an idele of $L$ (a unit of $\mathbb{A}_L$) and let $\alpha \in L^\times$, and write $x = u \cdot \iota_L(\alpha)^{-1}$, where $\iota_L$ is the diagonal embedding of units. Assume: (i) for every height-one prime $w$ of $\mathcal{O}_L$ dividing $\mathfrak{f}\mathcal{O}_L$, the finite component $x_w$ satisfies $v_w(x_w) = 1$ and $v_w(x_w - 1) \le \exp(-m_w)$, where $m_w$ is the multiplicity of $w$ in the factorisation of $\mathfrak{f}\mathcal{O}_L$; (ii) for every real infinite place $w$ of $L$, the infinite component of $x$ at $w$ is strictly positive when read through the real extension embedding of the completion. The conclusion is the same pair of clauses for $y = \mathrm{N}_B(u) \cdot \iota_K(\mathrm{N}_{L/K}\alpha)^{-1}$ over $K$: at every height-one prime $v$ of $\mathcal{O}_K$ dividing $\mathfrak{f}$ one has $v_v(y_v) = 1$ and $v_v(y_v - 1) \le \exp(-m_v)$ with $m_v$ the multiplicity of $v$ in $\mathfrak{f}$, and at every real infinite place $v$ of $K$ the component of $y$ is strictly positive.
--
--   This is the statement that the defining conditions of a ray-class level structure — congruence to $1$ modulo the conductor at the finite places, positivity at the real places — are preserved by the norm map from ideles of $L$ to ideles of $K$, in the adelic form needed here; no Galois, cyclicity or splitting hypothesis on $L/K$ is imposed. It is used in the construction of Hecke characters, where it feeds [`HeckeCharacter.isAdjuster_idelicNorm_of_isAdjuster`](thm.html#HeckeCharacter.isAdjuster_idelicNorm_of_isAdjuster).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_idelicNorm_levelCongr_and_realPos.lean

import Definitions.Def_M4aHerbrand_AdeleBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand

theorem M4aHerbrand.idelicNorm_levelCongr_and_realPos
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 L) L)ˣ) (α : Lˣ)
    (hcong : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ 𝔣.map (algebraMap (𝓞 K) (𝓞 L)) →
      Valued.v ((((u * (Units.map (algebraMap L (AdeleRing (𝓞 L) L)) α)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
          AdeleRing (𝓞 L) L).2 : FiniteAdeleRing (𝓞 L) L) w) = 1 ∧
        Valued.v ((((u * (Units.map (algebraMap L (AdeleRing (𝓞 L) L)) α)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
            AdeleRing (𝓞 L) L).2 : FiniteAdeleRing (𝓞 L) L) w - 1) ≤
          WithZero.exp (-((Associates.mk w.asIdeal).count
            (Associates.mk (𝔣.map (algebraMap (𝓞 K) (𝓞 L)))).factors : ℤ)))
    (hpos : ∀ (w : InfinitePlace L) (hw : w.IsReal),
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        ((((u * (Units.map (algebraMap L (AdeleRing (𝓞 L) L)) α)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
          AdeleRing (𝓞 L) L).1 : InfiniteAdeleRing L) w)) :
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v ((((B.idelicNorm u *
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.map (Algebra.norm K) α))⁻¹ :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 ∧
        Valued.v ((((B.idelicNorm u *
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.map (Algebra.norm K) α))⁻¹ :
              (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1) ≤
          WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ))) ∧
    ∀ (v : InfinitePlace K) (hv : v.IsReal),
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
        ((((B.idelicNorm u *
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.map (Algebra.norm K) α))⁻¹ :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) v) := by sorry
