-- Prove2me | Theorems.Thm_NumberField_Idele_contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact
-- name    : NumberField.Idele.contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/f6615693-ff81-5c83-bd01-6cdc4d491bcc
-- title:
--   The ξ-fold of local windows is a global window
-- statement:
--   Let $K$ be a number field, equip the idele unit group $(\mathbb{A}_K)^\times$ with a Borel measurable structure and let $\nu$ be a Haar measure on it, let $S$ be a finite set of nonzero primes of $\mathcal{O}_K$, and let $\xi$ be a homomorphism from the full subgroup $\top \le (\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ whose associated $\mathbb{C}$-valued function $z \mapsto \xi(z)$ is continuous. Let $\Phi_a : (\mathrm{Fin}\,2 \to \mathrm{mixedSpace}\,K) \to \mathbb{C}$ be $C^\infty$ with compact support, let $C_a$ be a compact set of units of the infinite adele ring, and assume that whenever $\Phi_a(p) \neq 0$ the preimage of $p_1$ under the ring equivalence $\mathrm{InfiniteAdeleRing}\,K \cong \mathrm{mixedSpace}\,K$ lies in the image of $C_a$ under $\mathrm{Units.val}$. For each finite place $v$ let $\Phi_f(v) : K_v \times K_v \to \mathbb{C}$, and assume for $v \in S$ that $\Phi_f(v)$ is locally constant, has compact support, and vanishes unless both of its arguments are nonzero. Let $\nu_S$ be the push-forward along [`NumberField.Idele.partAt K S`](def/NumberField_IdeleProductMeasure.html#L90) — the map induced on units by $(a_\infty, a_f) \mapsto (a_\infty, \mathrm{truncFin}\,K\,S\,a_f)$ — of the restriction of $\nu$ to the subgroup of those unit ideles $\delta$ for which, at every $v \notin S$, the $v$-components of the finite parts of both $\delta$ and $\delta^{-1}$ lie in $\mathcal{O}_v$. Put
--   $$W(x,b) \;=\; \int \xi(z)\,\Bigl(\Phi_a\bigl(x,\ \iota(z_\infty)\bigr)\,\prod_{v \in S} \Phi_f(v)(b_v, z_v)\Bigr)\, d\nu_S(z),$$
--   where $\iota$ is the above ring equivalence, $z_\infty$ and $(z_v)$ the infinite and finite parts of $z$, $x \in \mathrm{mixedSpace}\,K$ and $b \in \prod_v K_v$. The conclusion is the conjunction of four assertions: for every $b$, the function $x \mapsto W(x,b)$ is $C^\infty$; there is a compact $C \subseteq \mathrm{mixedSpace}\,K$ with $W(x,b) = 0$ for all $b$ and all $x \notin C$; for every $x$, the function $b \mapsto W(x,b)$ is locally constant; and there are sets $C_f(v) \subseteq K_v$, compact and not containing $0$ for $v \in S$, such that $W(x,b) = 0$ whenever $b_v \notin C_f(v)$ for some $v \in S$.
--
--   This is the realisation step which shows that folding a continuous idele class character against an archimedean window and finitely many local windows again produces a global window: smooth and compactly carried in the archimedean variable, locally constant and carried in compact subsets of $K_v^\times$ in the finite variables. It is used in the subsequent computations of orbital-type integrals and class sums attached to automorphic forms, where the resulting function of $(x,b)$ is fed into the summation formulae.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem NumberField.Idele.contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (Φa : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ) (hΦa : ContDiff ℝ (⊤ : ℕ∞) Φa) (hΦac : HasCompactSupport Φa)
    (Ca : Set (InfiniteAdeleRing K)ˣ) (hCa : IsCompact Ca)
    (hΦa0 : ∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Φa p ≠ 0 →
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1) ∈ Units.val '' Ca)
    (Φf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦf : ∀ v ∈ S, IsLocallyConstant (Φf v) ∧ HasCompactSupport (Φf v) ∧
      ∀ p, Φf v p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0) :
    (∀ b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K,
      ContDiff ℝ (⊤ : ℕ∞) fun x : mixedEmbedding.mixedSpace K =>
        ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (Φa ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) ∧
    (∃ C : Set (mixedEmbedding.mixedSpace K), IsCompact C ∧
      ∀ (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) (x : mixedEmbedding.mixedSpace K), x ∉ C →
        (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (Φa ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) = 0) ∧
    (∀ x : mixedEmbedding.mixedSpace K,
      IsLocallyConstant fun b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K =>
        ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (Φa ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) ∧
    (∃ Cf : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K), (∀ v ∈ S, IsCompact (Cf v) ∧ (0 : v.adicCompletion K) ∉ Cf v) ∧
      ∀ (x : mixedEmbedding.mixedSpace K) (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K),
        (∃ v ∈ S, b v ∉ Cf v) →
        (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (Φa ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) = 0) := by sorry
