-- Prove2me | Theorems.Thm_NumberField_Idele_integral_mul_kinkWindow_prod_map_partAt_eq_add_sum_real_add_sum_complex_of_isCompact
-- name    : NumberField.Idele.integral_mul_kinkWindow_prod_map_partAt_eq_add_sum_real_add_sum_complex_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/c3ebc8c3-0576-5407-83d9-78c7f24abb56
-- title:
--   Splitting of the idelic ξ-fold of a kinked archimedean window
-- statement:
--   Let $K$ be a number field, equip the idele unit group $(\mathbf{A}_K)^\times$ with a Borel measurable structure and let $\nu$ be a Haar measure on it. Fix a finite set $S$ of finite places of $K$, a homomorphism $\xi$ from the full subgroup $\top$ of $(\mathbf{A}_K)^\times$ to $\mathbb{C}^\times$ whose associated $\mathbb{C}$-valued function $z \mapsto \xi(z)$ is continuous, functions $B$ and $C_w, E_w$ (one pair for each infinite place $w$) on pairs of points of the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$, each smooth of all orders over $\mathbb{R}$ and compactly supported, a compact set $Ca$ of units of the infinite adele ring such that whenever $B p \neq 0$ or $C_w p \neq 0$ or $E_w p \neq 0$ for some $w$, the infinite adele corresponding to the second entry $p\,1$ lies in the set of underlying values of elements of $Ca$, and for each $v \in S$ a function $\Phi_v$ on pairs of elements of the completion $K_v$ which is locally constant, compactly supported and vanishes unless both entries are nonzero. Then for every $x$ in the mixed space and every family $b = (b_v)_v$ with $b_v \in K_v$, integration against the pushforward, along [`NumberField.Idele.partAt K S`](def/NumberField_IdeleProductMeasure.html#L90) (the unit map induced by replacing the finite part $a$ of an adele by its truncation `truncFin K S a` outside $S$), of the restriction of $\nu$ to the subgroup of idele units $\delta$ whose finite components satisfy $\delta_v$ and $(\delta^{-1})_v \in \mathcal{O}_{K_v}$ for all $v \notin S$, satisfies the following identity. The integral of $$\xi(z)\Bigl(B + \sum_{w\ \text{real}} \|(1-x)_w\|\,C_w + \sum_{w\ \text{complex}} \|(1-x)_w\|^2\log\|(1-x)_w\|\,E_w\Bigr)\bigl(x, \iota(z_\infty)\bigr) \prod_{v \in S} \Phi_v(b_v, z_v)$$ equals the corresponding integral with $B$ alone, plus $\sum_{w\ \text{real}} \|(1-x)_w\|$ times the integral with $C_w$, plus $\sum_{w\ \text{complex}} \|(1-x)_w\|^2\log\|(1-x)_w\|$ times the integral with $E_w$. Here $\iota$ denotes `InfiniteAdeleRing.ringEquiv_mixedSpace K`, $z_\infty$ the infinite part of $z$, and $\|(1-x)_w\|$ the norm in $K_w$ of the value at $w$ (`archEval K w`) of $1 - \iota^{-1}(x)$.
--
--   This is the linearity step that transports a kinked archimedean window through the idelic $\xi$-fold: since the kink factors $\|(1-x)_w\|$ and $\|(1-x)_w\|^2\log\|(1-x)_w\|$ depend only on the parameter $x$ and not on the integration variable, the fold of the kinked window is the same combination of the folds of the smooth pieces $B$, $C_w$, $E_w$. It feeds the construction of windows with prescribed archimedean discrepancy and the resulting class-sum identities for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_integral_mul_kinkWindow_prod_map_partAt_eq_add_sum_real_add_sum_complex_of_isCompact.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem NumberField.Idele.integral_mul_kinkWindow_prod_map_partAt_eq_add_sum_real_add_sum_complex_of_isCompact
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (B : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (C E : NumberField.InfinitePlace K → (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (hB : ContDiff ℝ (⊤ : ℕ∞) B ∧ HasCompactSupport B)
    (hC : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (C w) ∧ HasCompactSupport (C w))
    (hE : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (E w) ∧ HasCompactSupport (E w))
    (Ca : Set (InfiniteAdeleRing K)ˣ) (hCa : IsCompact Ca)
    (h0 : ∀ p : Fin 2 → mixedEmbedding.mixedSpace K, (B p ≠ 0 ∨ ∃ w, C w p ≠ 0 ∨ E w p ≠ 0) →
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1) ∈ Units.val '' Ca)
    (Φf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦf : ∀ v ∈ S, IsLocallyConstant (Φf v) ∧ HasCompactSupport (Φf v) ∧
      ∀ p, Φf v p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0)
    (x : mixedEmbedding.mixedSpace K) (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) :
    (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          ((fun p : Fin 2 → mixedEmbedding.mixedSpace K =>
            B p +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ : ℝ) : ℂ) * C w p +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ ^ 2 *
                Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ : ℝ) : ℂ) * E w p) ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) =
      (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (B ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) +
      ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal),
        ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)‖ : ℝ) : ℂ) *
        (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (C w ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) +
      ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex),
        ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)‖ ^ 2 *
              Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)‖ : ℝ) : ℂ) *
        (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (E w ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) := by sorry
