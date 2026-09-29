-- Prove2me | Theorems.Thm_M4aHerbrand_finSIdeleFibreBox_tateCard_eq_localDegreeProd
-- name    : M4aHerbrand.finSIdeleFibreBox_tateCard_eq_localDegreeProd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/3488b239-f8fc-508f-90a1-7bf5e9c360e7
-- title:
--   Herbrand quotient of the fibre-and-box finite S-idele group
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $\sigma \in \operatorname{Gal}(L/K)$ be such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$, and let $S$ be a finite set of height-one primes of $\mathcal{O}_K$ such that every prime $w$ of $\mathcal{O}_L$ whose contraction to $\mathcal{O}_K$ lies outside $S$ has ramification index $1$ over that contraction. Let $D$ be an idele Galois descent datum for $(\mathcal{O}_L, K, L)$, that is, a monoid homomorphism from $\operatorname{Gal}(L/K)$ to the ring automorphisms of the adele ring of $L$, compatible with the structure map of $L$ and continuous in each component. Assume given, for each $v \in S$, a multiplicative automorphism $\Phi^{\mathrm f}_v$ of $\bigl(\prod_{w \mid v} L_w\bigr)^{\times}$ and, for each $v \notin S$, a multiplicative automorphism $\Phi^{\mathrm b}_v$ of $\bigl(\prod_{w \mid v} \mathcal{O}_{L_w}\bigr)^{\times}$, each computing the coordinates at the places above $v$ of the finite part of $D.\mathrm{act}\,\sigma$ applied to $(1,x)$, for every finite adele $x$ of $L$ whose coordinates above $v$ are given by the chosen unit. Let $A$ denote the additively written group $\bigl(\prod_{v \in S}(\prod_{w\mid v} L_w)^{\times}\bigr) \times \bigl(\prod_{v \notin S}(\prod_{w\mid v}\mathcal{O}_{L_w})^{\times}\bigr)$, and let $d, N : A \to A$ be additive endomorphisms with $d(u) = \Phi(u) - u$ and $N(u) = \sum_{i < n} \Phi^{i}(u)$, where $\Phi$ acts componentwise by the $\Phi^{\mathrm f}_v$ and $\Phi^{\mathrm b}_v$ and $n = \#\operatorname{Gal}(L/K)$. Finally let $s_v = \#\{w \mid v\}$ for every $v$. Then $\#\bigl(\ker d / (\operatorname{im} N \cap \ker d)\bigr) = \prod_{v \in S} n / s_v$ (natural-number division) and $\#\bigl(\ker N / (\operatorname{im} d \cap \ker N)\bigr) = 1$.
--
--   This is the finite-places half of the Herbrand quotient computation for a cyclic extension of number fields: the two quotients are the Tate cohomology groups $\hat H^{0}$ and $\hat H^{-1}$ of the fibre-and-box $S$-idele module, and the factors $n/s_v$ are the local degrees $[L_w : K_v]$ at $v \in S$. It is used by [`M4aHerbrand.finSIdele_tateCard_eq_localDegreeProd`](thm.html#M4aHerbrand.finSIdele_tateCard_eq_localDegreeProd), which transfers the count to the flat finite $S$-idele carrier.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_finSIdeleFibreBox_tateCard_eq_localDegreeProd.lean

import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.FieldTheory.Galois.Basic
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open NumberField IsDedekindDomain

theorem M4aHerbrand.finSIdeleFibreBox_tateCard_eq_localDegreeProd
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

    (hSram : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
      (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1)

    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) →
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ ≃*
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ)
    (hΦf : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S})
      (u : (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ)
      (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        x w.1 = (u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          w.1.adicCompletion L) w) →
      ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 =
          (Φf v u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
            w.1.adicCompletion L) w)

    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) →
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ ≃*
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ)
    (hΦb : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
      (u : (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ)
      (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        x w.1 = ((u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)) →
      ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 =
          ((Φb v u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
            ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L))

    (d : Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)) →+
      Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)))
    (hd : ∀ u, d (Additive.ofMul u) =
      Additive.ofMul ((fun v => Φf v (u.1 v), fun v => Φb v (u.2 v))) - Additive.ofMul u)
    (N : Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)) →+
      Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)))
    (hN : ∀ u, N (Additive.ofMul u) =
      ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)),
        Additive.ofMul ((fun v => (Φf v ^ i) (u.1 v), fun v => (Φb v ^ i) (u.2 v))))

    (sf : HeightOneSpectrum (𝓞 K) → ℕ)
    (hsf : ∀ v, sf v = Nat.card {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker)
        = ∏ v ∈ S, Nat.card (L ≃ₐ[K] L) / sf v
      ∧ Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker) = 1 := by sorry
